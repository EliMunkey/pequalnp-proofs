import PetersenPhysicalBoundary
import Mathlib.Data.Nat.Bitwise

open PetersenSignedBridge

namespace PetersenFiniteDSL

inductive Mode where | signed | physical
deriving DecidableEq, Repr

/-- A signed operand is a possibly complemented existing wire or the constant zero.
The physical program has its two constants and both polarities of x₀ in its initial rails. -/
def Arg : Mode → Nat → Type
  | .signed, n => Option (Fin n) × Bool
  | .physical, n => Fin n

def pick {Ω : Type} {n : Nat} (w : Fin n → Func Ω) : Option (Fin n) → Func Ω
  | none => fun _ => false
  | some i => w i

def value {Ω : Type} {n : Nat} (m : Mode) (w : Fin n → Func Ω) : Arg m n → Func Ω :=
  match m with
  | .signed => fun (a,s) => if s then fun x => !(pick w a x) else pick w a
  | .physical => fun i => w i

abbrev Gate (m : Mode) (n : Nat) := Bool × Arg m n × Arg m n

def gateValue {Ω : Type} {n : Nat} (m : Mode) (w : Fin n → Func Ω) (g : Gate m n) : Func Ω :=
  fun x => if g.1 then value m w g.2.1 x || value m w g.2.2 x
                    else value m w g.2.1 x && value m w g.2.2 x

/-- The last gate has two bounded operands referencing only inputs and earlier gates. -/
def Program (m : Mode) (n : Nat) : Nat → Type
  | 0 => Unit
  | k+1 => Program m n k × Gate m (n+k)

def state {Ω : Type} (m : Mode) (init : List (Func Ω)) :
    (k : Nat) → Program m init.length k → Fin (init.length+k) → Func Ω
  | 0, _ => init.get
  | k+1, (p,g) =>
    let w := state m init k p
    Fin.cons (gateValue m w g) w

abbrev Output (m : Mode) (n k : Nat) := Program m n k × Arg m (n+k)

def output {Ω : Type} (m : Mode) (init : List (Func Ω)) (k : Nat)
    (p : Output m init.length k) : Func Ω :=
  value m (state m init k p.1) p.2

private theorem list_start {Ω : Type} (m : Mode) (init : List (Func Ω)) :
    List.ofFn (state m init 0 ()) = init := by simp [state]

private theorem list_step {Ω : Type} {m : Mode} {init : List (Func Ω)} {k : Nat}
    (p : Program m init.length k) (g : Gate m (init.length+k)) :
    List.ofFn (state m init (k+1) (p,g)) =
      gateValue m (state m init k p) g :: List.ofFn (state m init k p) := by
  simp [state,List.ofFn_succ]

private theorem value_signed {Ω : Type} {n : Nat} {w : Fin n → Func Ω}
    (a : Arg .signed n) : Av (List.ofFn w) (value .signed w a) := by
  rcases a with ⟨o,s⟩
  cases o with
  | none => cases s <;> first | exact Av.zero | exact Av.neg Av.zero
  | some i =>
    have h : Av (List.ofFn w) (w i) := Av.wire (List.mem_ofFn.mpr ⟨i,rfl⟩)
    cases s <;> first | exact h | exact Av.neg h

private theorem encode_signed {Ω : Type} {n : Nat} {w : Fin n → Func Ω} {f : Func Ω}
    (h : Av (List.ofFn w) f) : ∃ a : Arg .signed n, value .signed w a = f := by
  induction h with
  | wire hi =>
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hi
    exact ⟨(some i,false),rfl⟩
  | zero => exact ⟨(none,false),rfl⟩
  | one => exact ⟨(none,true),rfl⟩
  | neg h ih =>
    obtain ⟨⟨a,s⟩,rfl⟩ := ih
    refine ⟨(a,!s),?_⟩
    cases s <;> funext x <;> simp [value]

/-- Both semantics match the mathematical circuit relations exactly, preserving the
entire environment at every gate, including unreachable and repeated wires. -/
theorem decode_signed {Ω : Type} (init : List (Func Ω)) :
    ∀ (k : Nat) (p : Program .signed init.length k), Run init k (List.ofFn (state .signed init k p))
  | 0, () => by rw [list_start]; exact Run.start
  | k+1, (p,g) => by
    rw [list_step]
    obtain ⟨op,a,b⟩ := g
    have h := decode_signed init k p
    cases op
    · exact Run.and h (value_signed a) (value_signed b)
    · exact Run.or h (value_signed a) (value_signed b)

theorem decode_direct {Ω : Type} (init : List (Func Ω)) :
    ∀ (k : Nat) (p : Program .physical init.length k), Direct init k (List.ofFn (state .physical init k p))
  | 0, () => by rw [list_start]; exact Direct.start
  | k+1, (p,g) => by
    rw [list_step]
    obtain ⟨op,a,b⟩ := g
    have h := decode_direct init k p
    cases op
    · exact Direct.and h (List.mem_ofFn.mpr ⟨a,rfl⟩) (List.mem_ofFn.mpr ⟨b,rfl⟩)
    · exact Direct.or h (List.mem_ofFn.mpr ⟨a,rfl⟩) (List.mem_ofFn.mpr ⟨b,rfl⟩)

theorem encode_run {Ω : Type} {init W : List (Func Ω)} {k : Nat} (r : Run init k W) :
    ∃ p : Program .signed init.length k, List.ofFn (state .signed init k p) = W := by
  induction r with
  | start => exact ⟨(),list_start ..⟩
  | and _ ha hb ih =>
    obtain ⟨p,rfl⟩ := ih
    obtain ⟨a,rfl⟩ := encode_signed ha
    obtain ⟨b,rfl⟩ := encode_signed hb
    exact ⟨(p,false,a,b),list_step ..⟩
  | or _ ha hb ih =>
    obtain ⟨p,rfl⟩ := ih
    obtain ⟨a,rfl⟩ := encode_signed ha
    obtain ⟨b,rfl⟩ := encode_signed hb
    exact ⟨(p,true,a,b),list_step ..⟩

theorem encode_direct {Ω : Type} {init W : List (Func Ω)} {k : Nat} (r : Direct init k W) :
    ∃ p : Program .physical init.length k, List.ofFn (state .physical init k p) = W := by
  induction r with
  | start => exact ⟨(),list_start ..⟩
  | and _ ha hb ih =>
    obtain ⟨p,rfl⟩ := ih
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨b,rfl⟩ := List.mem_ofFn.mp hb
    exact ⟨(p,false,a,b),list_step ..⟩
  | or _ ha hb ih =>
    obtain ⟨p,rfl⟩ := ih
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨b,rfl⟩ := List.mem_ofFn.mp hb
    exact ⟨(p,true,a,b),list_step ..⟩

theorem signed_iff {Ω : Type} {init : List (Func Ω)} {k : Nat} {t : Func Ω} :
    (∃ W, Run init k W ∧ Av W t) ↔ ∃ p, output .signed init k p = t := by
  constructor
  · rintro ⟨W,r,h⟩
    obtain ⟨p,rfl⟩ := encode_run r
    obtain ⟨a,eq⟩ := encode_signed h
    exact ⟨(p,a),eq⟩
  · rintro ⟨⟨p,a⟩,rfl⟩
    exact ⟨_,decode_signed init k p,value_signed a⟩

theorem physical_iff {Ω : Type} {init : List (Func Ω)} {k : Nat} {t : Func Ω} :
    (∃ W, Direct init k W ∧ t ∈ W) ↔ ∃ p, output .physical init k p = t := by
  constructor
  · rintro ⟨W,r,h⟩
    obtain ⟨p,rfl⟩ := encode_direct r
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    exact ⟨(p,i),rfl⟩
  · rintro ⟨⟨p,a⟩,rfl⟩
    exact ⟨_,decode_direct init k p,List.mem_ofFn.mpr ⟨a,rfl⟩⟩


/-- Constructive choices for one operand. Every list here is explicitly computed. -/
def operands (m : Mode) (n : Nat) : List (Arg m n) :=
  match m with
  | .physical => List.finRange n
  | .signed => (none :: (List.finRange n).map some).product [false,true]

theorem mem_operands {m : Mode} {n : Nat} (a : Arg m n) : a ∈ operands m n := by
  cases m with
  | physical => exact List.mem_finRange a
  | signed =>
    rcases a with ⟨o,s⟩
    apply List.mem_product.mpr
    constructor
    · cases o with
      | none => exact List.mem_cons_self ..
      | some i => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
    · cases s <;> simp

def gates (m : Mode) (n : Nat) : List (Gate m n) :=
  [false,true].product ((operands m n).product (operands m n))

theorem mem_gates {m : Mode} {n : Nat} (g : Gate m n) : g ∈ gates m n := by
  rcases g with ⟨s,a,b⟩
  exact List.mem_product.mpr ⟨by cases s <;> simp,List.mem_product.mpr ⟨mem_operands a,mem_operands b⟩⟩

def programs (m : Mode) (n : Nat) : (k : Nat) → List (Program m n k)
  | 0 => [()]
  | k+1 => (programs m n k).product (gates m (n+k))

theorem mem_programs (m : Mode) (n : Nat) : ∀ (k : Nat) (p : Program m n k), p ∈ programs m n k
  | 0, () => List.mem_cons_self ..
  | k+1, (p,g) => List.mem_product.mpr ⟨mem_programs m n k p,mem_gates g⟩

/-- Finite row coverage uses the same low-bit-first ordering as the search. -/
private theorem represented : ∀ n (x : Fin n → Bool),
    ∃ r < 2^n, ∀ i : Fin n, r.testBit i.val = x i
  | 0, _ => ⟨0,by decide,fun i => Fin.elim0 i⟩
  | n+1, x => by
    obtain ⟨r,hr,h⟩ := represented n (Fin.tail x)
    refine ⟨Nat.bit (x 0) r,?_,?_⟩
    · rw [pow_succ]
      cases x 0 <;> simp only [Nat.bit_false,Nat.bit_true] <;> omega
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Nat.testBit_bit_zero _ _
      · exact (Nat.testBit_bit_succ ..).trans (h j)

theorem all_rows (x : PInput) : ∃ r < 1024, PhysicalBoundary.word r = x := by
  obtain ⟨r,hr,h⟩ := represented 10 x
  exact ⟨r,hr,funext h⟩

/-- A completely finite reference decider. A certified pruning algorithm need only
refine this meaning; it is never necessary to materialize the full tuple list. -/
def checkAt (m : Mode) (init : List (Func PInput)) (k : Nat) (rows : List Nat)
    (target : Func PInput) : Bool :=
  (programs m init.length k).all fun p =>
    (operands m (init.length+k)).all fun a =>
      rows.any fun r =>
        let x := PhysicalBoundary.word r
        output m init k (p,a) x != target x

theorem checkAt_iff (m : Mode) (init : List (Func PInput)) (k : Nat) (rows : List Nat)
    (target : Func PInput) :
    checkAt m init k rows target = true ↔
      ∀ p : Output m init.length k, ∃ r ∈ rows,
        output m init k p (PhysicalBoundary.word r) ≠ target (PhysicalBoundary.word r) := by
  constructor
  · intro h p
    obtain ⟨pg,a⟩ := p
    have u := List.all_eq_true.mp h pg (mem_programs ..)
    have v := List.all_eq_true.mp u a (mem_operands a)
    simpa only [List.any_eq_true,bne_iff_ne] using v
  · intro h
    apply List.all_eq_true.mpr
    intro p _
    apply List.all_eq_true.mpr
    intro a _
    simpa only [List.any_eq_true,bne_iff_ne] using h (p,a)

def signedCheck : Bool :=
  (List.range 18).all fun k => checkAt .signed base k (List.range 1024) PetersenTarget

def physicalCheck : Bool :=
  checkAt .physical rails 18 PhysicalBoundary.selected PetersenTarget

theorem signedCheck_iff :
    signedCheck = true ↔ ∀ k ≤ 17, ∀ W, Run base k W → ¬Av W PetersenTarget := by
  constructor
  · intro h k hk W rwf htarget
    obtain ⟨p,he⟩ := signed_iff.mp ⟨W,rwf,htarget⟩
    have good := List.all_eq_true.mp h k (List.mem_range.mpr (by omega))
    obtain ⟨r,_,hne⟩ := (checkAt_iff ..).mp good p
    exact hne (congrFun he _)
  · intro h
    apply List.all_eq_true.mpr
    intro k hk
    apply (checkAt_iff ..).mpr
    intro p
    by_contra! agrees
    have he : output .signed base k p = PetersenTarget := by
      funext x
      obtain ⟨r,hr,rfl⟩ := all_rows x
      exact agrees r (List.mem_range.mpr hr)
    obtain ⟨W,r,ht⟩ := signed_iff.mpr ⟨p,he⟩
    exact h k (by have := List.mem_range.mp hk; omega) W r ht

theorem physicalCheck_iff :
    physicalCheck = true ↔ ∀ W, Direct rails 18 W → PetersenTarget ∉ W := by
  constructor
  · intro h W r ht
    obtain ⟨p,he⟩ := physical_iff.mp ⟨W,r,ht⟩
    obtain ⟨x,_,bad⟩ := (checkAt_iff ..).mp h p
    exact bad (congrFun he _)
  · intro h
    apply (checkAt_iff ..).mpr
    intro p
    by_contra! agrees
    obtain ⟨pg,a⟩ := p
    have run := decode_direct rails 18 pg
    have mem : output .physical rails 18 (pg,a) ∈ _ :=
      List.mem_ofFn.mpr ⟨a,rfl⟩
    have full := (PhysicalBoundary.physical_compressed_iff run mem).mpr agrees
    have he : output .physical rails 18 (pg,a) = PetersenTarget := by
      funext x
      obtain ⟨r,hr,rfl⟩ := all_rows x
      exact full r hr
    exact h _ run (he ▸ mem)

/-- The standard checker kernel can validate any proof of these two finite Bool values. -/
theorem L_meta_1884_of_finite_checks (hs : signedCheck = true) (hp : physicalCheck = true) :
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool),
    PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 18 →
    ∃ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ PetersenTarget x :=
  L_meta_1884_of_exclusions (signedCheck_iff.mp hs) (physicalCheck_iff.mp hp)

private def x0 : Func PInput := fun x => x 0
private def x1 : Func PInput := fun x => x 1
private def minterm : Func PInput := fun x => !x 0 && x 1

/-- Run the reference checker in the kernel on cases that distinguish the two bases. -/
theorem reference_controls :
    checkAt .signed [x0,x1] 0 [0,1,2,3] minterm = true ∧
    checkAt .signed [x0,x1] 1 [0,1,2,3] minterm = false ∧
    checkAt .physical [x0,x1] 1 [0,1,2,3] minterm = true ∧
    checkAt .physical [x0,x1,fun x => !x 0] 1 [0,1,2,3] minterm = false := by decide

#print axioms reference_controls
#print axioms L_meta_1884_of_finite_checks
end PetersenFiniteDSL
