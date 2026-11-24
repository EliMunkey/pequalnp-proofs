import PEqualNP.Defs.MetaComplexity
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Convert

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenSignedBridge

abbrev Func (Ω : Type) := Ω → Bool

/-- Free constants and both signs of an existing wire. -/
inductive Av {Ω : Type} (W : List (Func Ω)) : Func Ω → Prop where
  | wire {f} : f ∈ W → Av W f
  | zero : Av W (fun _ => false)
  | one : Av W (fun _ => true)
  | neg {f} : Av W f → Av W (fun x => !(f x))

/-- An unrestricted signed two-input straight-line circuit, with only binary operations charged. -/
inductive Run {Ω : Type} (init : List (Func Ω)) : Nat → List (Func Ω) → Prop where
  | start : Run init 0 init
  | and {k W a b} : Run init k W → Av W a → Av W b →
      Run init (k+1) ((fun x => a x && b x)::W)
  | or {k W a b} : Run init k W → Av W a → Av W b →
      Run init (k+1) ((fun x => a x || b x)::W)

def paid (g : Gate) : Bool :=
  match g.op, g.inputs with
  | .and, [_,_] | .or, [_,_] => true
  | _,_ => false

theorem branch (C : Circuit) (h : C.size ≤ 18) :
    (C.gates.filter paid).length ≤ 17 ∨
    C.size = 18 ∧ ∀ g ∈ C.gates, paid g = true := by
  by_cases small : (C.gates.filter paid).length ≤ 17
  · exact Or.inl small
  · right
    have le : (C.gates.filter paid).length ≤ C.gates.length := List.length_filter_le _ _
    change C.gates.length ≤ 18 at h
    have eq : (C.gates.filter paid).length = C.gates.length := by omega
    exact ⟨by change C.gates.length = 18; omega, List.length_filter_eq_length_iff.mp eq⟩

variable {Ω : Type}

private theorem wk {W : List (Func Ω)} {f g : Func Ω} (h : Av W f) : Av (g::W) f := by
  induction h with
  | wire e => exact Av.wire (List.mem_cons_of_mem _ e)
  | zero => exact Av.zero
  | one => exact Av.one
  | neg _ ih => exact Av.neg ih

private theorem getAv {W L : List (Func Ω)} (h : ∀ f ∈ L, Av W f) (i : Nat) :
    Av W (L.getD i (fun _ => false)) := by
  induction L generalizing i with
  | nil => simp [List.getD]; exact Av.zero
  | cons a as ih =>
    cases i with
    | zero => simpa [List.getD] using h a (by simp)
    | succ i =>
      simpa [List.getD] using ih (fun v hv => h v (List.mem_cons_of_mem _ hv)) i

def sym (g : Gate) (L : List (Func Ω)) : Func Ω :=
  fun x => g.op.eval (g.inputs.map fun i => (L.getD i (fun _ => false)) x)

theorem compile_gate {init W L : List (Func Ω)} {k : Nat} (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not}:Set GateOp) ∧ g.inputs.length ≤ 2)
    (run : Run init k W) (cov : ∀ f ∈ L, Av W f) :
    ∃ W', Run init (k+(if paid g then 1 else 0)) W' ∧
      ∀ f ∈ L ++ [sym g L], Av W' f := by
  have old (f : Func Ω) (hf : Av W f) : ∀ v ∈ L++[f], Av W v := by
    intro v hv
    rcases List.mem_append.mp hv with e|e
    · exact cov _ e
    · exact List.mem_singleton.mp e ▸ hf
  have added (f : Func Ω) : ∀ v ∈ L++[f], Av (f::W) v := by
    intro v hv
    rcases List.mem_append.mp hv with e|e
    · exact wk (cov _ e)
    · exact List.mem_singleton.mp e ▸ Av.wire (List.mem_cons_self ..)
  obtain ⟨op,arity⟩ := hg
  rcases g with ⟨op',ins⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
  change op' = .and ∨ op' = .or ∨ op' = .not at op
  change ins.length ≤ 2 at arity
  rcases op with (rfl|rfl|rfl)
  · cases ins with
    | nil =>
      refine ⟨W,by simpa [paid] using run,?_⟩
      unfold sym
      simpa [GateOp.eval] using old (fun _ => true) Av.one
    | cons i tail =>
      cases tail with
      | nil =>
        refine ⟨W,by simpa [paid] using run,?_⟩
        unfold sym
        simpa [GateOp.eval] using old _ (getAv cov i)
      | cons j tail =>
        cases tail with
        | cons a tail => simp at arity
        | nil =>
          let f : Func Ω := fun x => (L.getD i (fun _ => false)) x && (L.getD j (fun _ => false)) x
          refine ⟨f::W,by simpa [paid,f] using (Run.and run (getAv cov i) (getAv cov j)),?_⟩
          unfold sym
          simpa [f,GateOp.eval] using added f
  · cases ins with
    | nil =>
      refine ⟨W,by simpa [paid] using run,?_⟩
      unfold sym
      simpa [GateOp.eval] using old (fun _ => false) Av.zero
    | cons i tail =>
      cases tail with
      | nil =>
        refine ⟨W,by simpa [paid] using run,?_⟩
        unfold sym
        simpa [GateOp.eval] using old _ (getAv cov i)
      | cons j tail =>
        cases tail with
        | cons a tail => simp at arity
        | nil =>
          let f : Func Ω := fun x => (L.getD i (fun _ => false)) x || (L.getD j (fun _ => false)) x
          refine ⟨f::W,by simpa [paid,f] using (Run.or run (getAv cov i) (getAv cov j)),?_⟩
          unfold sym
          simpa [f,GateOp.eval] using added f
  · cases ins with
    | nil =>
      refine ⟨W,by simpa [paid] using run,?_⟩
      unfold sym
      simpa [GateOp.eval] using old (fun _ => true) Av.one
    | cons i tail =>
      cases tail with
      | nil =>
        refine ⟨W,by simpa [paid] using run,?_⟩
        unfold sym
        simpa [GateOp.eval] using old _ (Av.neg (getAv cov i))
      | cons j tail =>
        cases tail with
        | cons a tail => simp at arity
        | nil =>
          refine ⟨W,by simpa [paid] using run,?_⟩
          unfold sym
          simpa [GateOp.eval] using old _ (Av.neg (getAv cov i))

def trace : List Gate → List (Func Ω) → List (Func Ω)
  | [], L => L
  | g::gs, L => trace gs (L++[sym g L])

private theorem compile (gs : List Gate) {init W L : List (Func Ω)} {k : Nat}
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not}:Set GateOp) ∧ g.inputs.length ≤ 2)
    (run : Run init k W) (cov : ∀ f ∈ L, Av W f) :
    ∃ W', Run init (k+(gs.filter paid).length) W' ∧ ∀ f ∈ trace gs L, Av W' f := by
  induction gs generalizing k W L with
  | nil => exact ⟨W,by simpa using run,cov⟩
  | cons g gs ih =>
    obtain ⟨W',hr,hc⟩ := compile_gate g (hg g (by simp)) run cov
    obtain ⟨W'',hr',hc'⟩ := ih (fun v hv => hg v (List.mem_cons_of_mem _ hv)) hr hc
    refine ⟨W'',?_,hc'⟩
    cases h : paid g <;> simp_all [Nat.add_comm,Nat.add_left_comm]

private theorem evget (L : List (Func Ω)) (x : Ω) (i : Nat) :
    (L.map (fun f => f x)).getD i false = (L.getD i (fun _ => false)) x :=
  List.getD_map L (fun _ => false) (fun f => f x)

private theorem eval_trace (gs : List Gate) (L : List (Func Ω)) (x : Ω) :
    (trace gs L).map (fun f => f x) =
      gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) (L.map (fun f => f x)) := by
  induction gs generalizing L with
  | nil => rfl
  | cons g gs ih => simp only [trace,List.foldl_cons,ih,List.map_append,List.map_cons,List.map_nil,sym,evget]

abbrev PInput := Fin 10 → Bool
def base : List (Func PInput) := List.ofFn (fun i x => x i)
def raw (σ : Fin 10 → Fin 10) (u : Bool → Bool) : List (Func PInput) :=
  List.ofFn (fun i x => x (σ i)) ++ [fun x => u (x 0)]

private theorem prime (i : Fin 10) : Av base (fun x => x i) :=
  Av.wire (List.mem_ofFn.mpr ⟨i,rfl⟩)

private theorem bonus (u : Bool → Bool) : Av base (fun x => u (x 0)) := by
  have eqf (f : Bool → Bool) (h : ∀ b, u b = f b) :
      (fun x : PInput => u (x 0)) = (fun x => f (x 0)) := by funext x; exact h _
  cases h0 : u false <;> cases h1 : u true
  · rw [eqf (fun _ => false) (by intro b; cases b <;> assumption)]
    exact Av.zero
  · rw [eqf id (by intro b; cases b <;> assumption)]
    exact prime 0
  · rw [eqf Bool.not (by intro b; cases b <;> assumption)]
    exact Av.neg (prime 0)
  · rw [eqf (fun _ => true) (by intro b; cases b <;> assumption)]
    exact Av.one

/-- The exact project evaluator compiles to signed straight-line gates, including its
out-of-range default, arbitrary input substitution and every possible unary bonus input. -/
theorem signed_realization (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (allowed : FanInTwo C) :
    ∃ W, Run base (C.gates.filter paid).length W ∧
      Av W (fun x => C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)])) := by
  have init : ∀ f ∈ raw σ u, Av base f := by
    intro f hf
    rcases List.mem_append.mp hf with h|h
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
      exact prime (σ i)
    · simp only [List.mem_singleton] at h
      exact h ▸ bonus u
  obtain ⟨W,hW,hcov⟩ := compile C.gates allowed (Run.start (init := base)) init
  refine ⟨W,by simpa using hW,?_⟩
  have hget := getAv hcov C.output
  convert hget using 1
  funext x
  rw [← evget (trace C.gates (raw σ u)) x C.output, eval_trace]
  simp [Circuit.eval,Circuit.wires,raw,Function.comp_def]

/-- It suffices to exclude signed circuits through 17 binary gates and the precise
18-gate binary AND/OR subclass of the project evaluator. -/
theorem close_branches (target : PInput → Bool)
    (signed : ∀ k ≤ 17, ∀ W, Run base k W → ¬ Av W target)
    (positive : ∀ (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool),
      C.size = 18 → (∀ g ∈ C.gates, paid g = true) →
      ∃ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ target x)
    (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (fan : FanInTwo C) (small : C.size ≤ 18) :
    ∃ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ target x := by
  rcases branch C small with low|⟨e,hg⟩
  · obtain ⟨W,r,h⟩ := signed_realization C σ u fan
    by_contra! agrees
    exact signed _ low W r ((funext agrees) ▸ h)
  · exact positive C σ u e hg


inductive Direct {Ω : Type} (init : List (Func Ω)) : Nat → List (Func Ω) → Prop where
  | start : Direct init 0 init
  | and {k W a b} : Direct init k W → a ∈ W → b ∈ W →
    Direct init (k+1) ((fun x => a x && b x)::W)
  | or {k W a b} : Direct init k W → a ∈ W → b ∈ W →
    Direct init (k+1) ((fun x => a x || b x)::W)

private theorem kept {init W : List (Func Ω)} {k} (r : Direct init k W) :
    ∀ f ∈ init, f ∈ W := by
  induction r with
  | start => exact fun _ h => h
  | and _ _ _ ih => exact fun f h => List.mem_cons_of_mem _ (ih f h)
  | or _ _ _ ih => exact fun f h => List.mem_cons_of_mem _ (ih f h)

private theorem getmem {L W : List (Func Ω)} (default : (fun _ => false) ∈ W)
    (cov : ∀ f ∈ L, f ∈ W) (i : Nat) : L.getD i (fun _ => false) ∈ W := by
  induction L generalizing i with
  | nil => simpa [List.getD] using default
  | cons a as ih =>
    cases i with
    | zero => simpa [List.getD] using cov a (by simp)
    | succ i => simpa [List.getD] using ih (fun v hv => cov v (List.mem_cons_of_mem _ hv)) i

private theorem paidShape (g : Gate) (hg : paid g) :
    ∃ i j, g = ⟨.and,[i,j]⟩ ∨ g = ⟨.or,[i,j]⟩ := by
  obtain ⟨op,ins⟩ := g
  cases op <;> cases ins with
  | nil => simp [paid] at hg
  | cons i rem =>
    cases rem with
    | nil => simp [paid] at hg
    | cons j tail =>
      cases tail <;> simp_all [paid]

private theorem compileDirect (gs : List Gate) {init W L : List (Func Ω)} {k : Nat}
    (hg : ∀ g ∈ gs, paid g = true) (zero : (fun _ => false) ∈ init)
    (run : Direct init k W) (cov : ∀ f ∈ L, f ∈ W) :
    ∃ W', Direct init (k+gs.length) W' ∧ ∀ f ∈ trace gs L, f ∈ W' := by
  induction gs generalizing k W L with
  | nil => exact ⟨W, by simpa using run, cov⟩
  | cons g gs ih =>
    have inputs := getmem (kept run _ zero) cov
    have pushed (f : Func Ω) : ∀ v ∈ L++[f], v ∈ f::W := by
      intro v hv
      rcases List.mem_append.mp hv with e|e
      · exact List.mem_cons_of_mem _ (cov _ e)
      · exact List.mem_singleton.mp e ▸ List.mem_cons_self ..
    have next : Direct init (k+1) ((sym g L)::W) := by
      obtain ⟨i,j,rfl|rfl⟩ := paidShape g (hg g (by simp))
      · unfold sym
        simpa [GateOp.eval] using (Direct.and run (inputs i) (inputs j))
      · unfold sym
        simpa [GateOp.eval] using (Direct.or run (inputs i) (inputs j))
    obtain ⟨W',hr,hc⟩ := ih (fun v hv => hg v (List.mem_cons_of_mem _ hv)) next (pushed _)
    exact ⟨W', by simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hr,hc⟩

def rails : List (Func PInput) :=
  (fun _ => false)::(fun _ => true)::(fun x => !(x 0))::base

private theorem rawmem (σ : Fin 10 → Fin 10) (u : Bool → Bool) :
    ∀ f ∈ raw σ u, f ∈ rails := by
  intro f hf
  have coord (j : Fin 10) : (fun x => x j) ∈ base := List.mem_ofFn.mpr ⟨j,rfl⟩
  rcases List.mem_append.mp hf with v|v
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp v
    simp [rails,coord]
  · obtain rfl := List.mem_singleton.mp v
    have shape (v : Bool → Bool) (hv : ∀ b, u b = v b) :
        (fun x : PInput => u (x 0)) = (fun x => v (x 0)) := funext (fun x => hv _)
    cases f0 : u false <;> cases f1 : u true
    · rw [shape (fun _ => false) (by intro b; cases b <;> assumption)]
      simp [rails]
    · rw [shape id (by intro b; cases b <;> assumption)]
      simp [rails,coord]
    · rw [shape Bool.not (by intro b; cases b <;> assumption)]
      simp [rails]
    · rw [shape (fun _ => true) (by intro b; cases b <;> assumption)]
      simp [rails]

theorem positive_realization (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (hg : ∀ g ∈ C.gates, paid g = true) :
    ∃ W, Direct rails C.size W ∧ (fun x => C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)])) ∈ W := by
  have initial : (fun _ => false) ∈ rails := by simp [rails]
  obtain ⟨W,hW,hcov⟩ := compileDirect C.gates hg initial (Direct.start (init := rails)) (rawmem σ u)
  refine ⟨W,by simpa [Circuit.size] using hW,?_⟩
  have hget := getmem (kept hW _ initial) hcov C.output
  convert hget using 1
  funext x
  rw [← evget (trace C.gates (raw σ u)) x C.output, eval_trace]
  simp [Circuit.eval,Circuit.wires,raw,Function.comp_def]

/-- These two independent enumeration exclusions suffice for every input map and every
legal FanInTwo gate list in the originally assigned proposition. -/
theorem close_rail_branches (target : PInput → Bool)
    (signed : ∀ k ≤ 17, ∀ W, Run base k W → ¬ Av W target)
    (positive : ∀ W, Direct rails 18 W → target ∉ W)
    (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (fan : FanInTwo C) (small : C.size ≤ 18) :
    ∃ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ target x := by
  apply close_branches target signed _ C σ u fan small
  intro D τ v hk hpos
  obtain ⟨W,r,h⟩ := positive_realization D τ v hpos
  by_contra! agrees
  exact positive W (hk ▸ r) ((funext agrees) ▸ h)


def PetersenTarget : PInput → Bool := (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)))

/-- The conclusion below is the original assigned proposition verbatim. -/
theorem L_meta_1884_of_exclusions
    (signed : ∀ k ≤ 17, ∀ W, Run base k W → ¬ Av W PetersenTarget)
    (positive : ∀ W, Direct rails 18 W → PetersenTarget ∉ W) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool → Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x3 (x6 (0 : Fin (10 : ℕ)))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 :=
  close_rail_branches PetersenTarget signed positive

#print axioms L_meta_1884_of_exclusions

/-- An AND/OR prefix which never recreates a constant or either polarity of an earlier
signal. Including retired earlier wires here is safe in the free-sign comparison. -/
inductive Fresh {Ω : Type} (init : List (Func Ω)) : Nat → List (Func Ω) → Prop where
  | start : Fresh init 0 init
  | and {k W a b} : Fresh init k W → a ∈ W → b ∈ W → ¬ Av W (fun x => a x && b x) →
    Fresh init (k+1) ((fun x => a x && b x)::W)
  | or {k W a b} : Fresh init k W → a ∈ W → b ∈ W → ¬ Av W (fun x => a x || b x) →
    Fresh init (k+1) ((fun x => a x || b x)::W)

private theorem liftAv {W S : List (Func Ω)} {f : Func Ω} (cv : ∀ v ∈ W, Av S v)
    (e : Av W f) : Av S f := by
  induction e with
  | wire h => exact cv _ h
  | zero => exact Av.zero
  | one => exact Av.one
  | neg _ ih => exact Av.neg ih

private theorem railsSigned : ∀ f ∈ rails, Av base f := by
  intro f hf
  rcases List.mem_cons.mp hf with rfl|hf
  · exact Av.zero
  rcases List.mem_cons.mp hf with rfl|hf
  · exact Av.one
  rcases List.mem_cons.mp hf with rfl|hf
  · exact Av.neg (prime 0)
  · exact Av.wire hf

private theorem appendCov {W S : List (Func Ω)} (f : Func Ω) (h : ∀ v ∈ W, Av S v) :
    ∀ v ∈ f::W, Av (f::S) v := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl|e
  · exact Av.wire (List.mem_cons_self ..)
  · exact wk (h v e)

/-- Every direct prefix either has a fresh realization at its full cost or a shorter
signed realization. In both cases all signals of the direct prefix remain available. -/
theorem fresh_split {k : Nat} {W : List (Func PInput)} (r : Direct rails k W) :
    (Fresh rails k W ∧ ∃ S, Run base k S ∧ ∀ v ∈ W, Av S v) ∨
    ∃ j < k, ∃ S, Run base j S ∧ ∀ v ∈ W, Av S v := by
  induction r with
  | start => exact Or.inl ⟨Fresh.start,base,Run.start,railsSigned⟩
  | and r ha hb ih =>
    rename_i k W a b
    let f : Func PInput := fun x => a x && b x
    rcases ih with ⟨fr,S,sr,cv⟩|⟨j,hj,S,sr,cv⟩
    · by_cases present : Av W f
      · right
        refine ⟨k,by omega,S,sr,?_⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl|hv
        · exact liftAv cv present
        · exact cv _ hv
      · exact Or.inl ⟨Fresh.and fr ha hb present, f::S, Run.and sr (cv _ ha) (cv _ hb), appendCov f cv⟩
    · exact Or.inr ⟨j+1,by omega,f::S,Run.and sr (cv _ ha) (cv _ hb),appendCov f cv⟩
  | or r ha hb ih =>
    rename_i k W a b
    let f : Func PInput := fun x => a x || b x
    rcases ih with ⟨fr,S,sr,cv⟩|⟨j,hj,S,sr,cv⟩
    · by_cases present : Av W f
      · right
        refine ⟨k,by omega,S,sr,?_⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl|hv
        · exact liftAv cv present
        · exact cv _ hv
      · exact Or.inl ⟨Fresh.or fr ha hb present, f::S, Run.or sr (cv _ ha) (cv _ hb), appendCov f cv⟩
    · exact Or.inr ⟨j+1,by omega,f::S,Run.or sr (cv _ ha) (cv _ hb),appendCov f cv⟩

/-- The unrestricted signed exclusion justifies skipping opposite-polarity duplicates
and constants in the positive 18-gate enumeration. -/
theorem L_meta_1884_of_fresh_exclusions
    (signed : ∀ k ≤ 17, ∀ W, Run base k W → ¬ Av W PetersenTarget)
    (positive : ∀ W, Fresh rails 18 W → PetersenTarget ∉ W) :
    ∀ (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool), FanInTwo C → C.size ≤ 18 →
      ∃ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ PetersenTarget x := by
  apply L_meta_1884_of_exclusions signed
  intro W r ht
  rcases fresh_split r with ⟨fr,_⟩|⟨j,hj,S,sr,cv⟩
  · exact positive W fr ht
  · exact signed j (by omega) S sr (cv _ ht)

#print axioms L_meta_1884_of_fresh_exclusions


namespace PhysicalBoundary

def word (r : Nat) : PInput := fun i => r.testBit i.val

/-- The product order within each slice of input zero. -/
def below (a b : Nat) : Bool := (a.testBit 0 == b.testBit 0) && ((a &&& b) == a)

def monotoneOnSlices (f : Func PInput) : Prop :=
  ∀ a b : Nat, below a b = true → f (word a) = true → f (word b) = true

private theorem coordUp (i : Fin 10) : monotoneOnSlices (fun x => x i) := by
  intro a b h t
  simp only [below,Bool.and_eq_true,beq_iff_eq] at h
  have sub : a &&& b = a := h.2
  have bits := congrArg (fun n : Nat => n.testBit i.val) sub
  change a.testBit i.val = true at t
  change b.testBit i.val = true
  simpa [Nat.testBit_and,t] using bits

private theorem complementZeroUp : monotoneOnSlices (fun x => !(x 0)) := by
  intro a b h t
  simp only [below,Bool.and_eq_true,beq_iff_eq] at h
  have z := h.1
  change (!a.testBit 0) = true at t
  change (!b.testBit 0) = true
  simpa [← z] using t

private theorem railsUp : ∀ f ∈ rails, monotoneOnSlices f := by
  intro f h
  rcases List.mem_cons.mp h with rfl|h
  · simp [monotoneOnSlices]
  rcases List.mem_cons.mp h with rfl|h
  · simp [monotoneOnSlices]
  rcases List.mem_cons.mp h with rfl|h
  · exact complementZeroUp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
  exact coordUp i

/-- Every physically available intermediate signal is monotone on each of the two
slices, regardless of previous sharing and the total number of gates. -/
theorem circuit_up {k W} (r : Direct rails k W) : ∀ f ∈ W, monotoneOnSlices f := by
  induction r with
  | start => exact railsUp
  | and _ ha hb ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · intro a b h t
      simp only [Bool.and_eq_true] at t ⊢
      exact ⟨ih _ ha a b h t.1, ih _ hb a b h t.2⟩
    · exact ih _ hf
  | or _ ha hb ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · intro a b h t
      simp only [Bool.or_eq_true] at t ⊢
      rcases t with t|t
      · exact Or.inl (ih _ ha a b h t)
      · exact Or.inr (ih _ hb a b h t)
    · exact ih _ hf

def selected : List Nat := [3,6,12,13,17,24,33,50,66,69,104,116,132,133,138,160,200,201,208,
  264,265,276,288,320,321,385,402,521,528,548,554,576,577,640,641,770,772,773]

def edge (r : Nat) := PetersenTarget (word r)
def boundary (r : Nat) : Bool :=
  (List.range 9).all fun j =>
    let i := j+1
    r.testBit i != edge r || edge (r ^^^ 2^i) != edge r

def witness (x : Nat) : Bool :=
  if edge x then selected.any fun y => edge y && below y x
  else selected.any fun y => !edge y && below x y

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem tables :
    (List.range 1024).filter boundary = selected ∧
    (List.range 1024).all witness = true ∧ selected.length = 38 := by decide

/-- Matching all 38 bits of the two-slice boundary exactly characterizes an
AND/OR circuit's correctness on all 1,024 rows. -/
theorem compressed_iff (f : Func PInput) (up : monotoneOnSlices f) :
    (∀ x < 1024, f (word x) = edge x) ↔ ∀ y ∈ selected, f (word y) = edge y := by
  constructor
  · intro h y hy
    exact h _ (List.mem_range.mp (List.mem_filter.mp (tables.1 ▸ hy)).1)
  · intro h x hx
    have w := List.all_eq_true.mp tables.2.1 x (List.mem_range.mpr hx)
    cases ex : edge x with
    | true =>
      simp only [witness,ex,ite_true,List.any_eq_true,Bool.and_eq_true] at w
      obtain ⟨y,hy,ey,le⟩ := w
      exact up y x le ((h y hy).trans ey)
    | false =>
      simp only [witness,ex,Bool.false_eq_true,ite_false,List.any_eq_true,Bool.and_eq_true,
                 Bool.not_eq_true'] at w
      obtain ⟨y,hy,ey,le⟩ := w
      cases fval : f (word x) with
      | false => rfl
      | true =>
        have bad := up x y le fval
        rw [h y hy,ey] at bad
        contradiction

theorem physical_compressed_iff {k W} (r : Direct rails k W) {f} (hf : f∈W) :
    (∀ x < 1024, f (word x) = edge x) ↔ ∀ y ∈ selected, f (word y) = edge y :=
  compressed_iff f (circuit_up r f hf)

#print axioms physical_compressed_iff
end PhysicalBoundary

end PetersenSignedBridge
