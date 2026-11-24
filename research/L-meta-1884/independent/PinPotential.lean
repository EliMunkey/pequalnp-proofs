import Std

namespace PinPotential

/-- An abstract value for a wire after some original inputs are fixed. -/
inductive Value where
  | unknown
  | fixed (value : Bool)
  deriving DecidableEq, Repr

def Value.known : Value → Nat
  | .unknown => 0 | .fixed _ => 1

def Value.agrees : Value → Bool → Prop
  | .unknown, _ => True | .fixed a, b => a = b

instance (p : Value → Prop) [DecidablePred p] : Decidable (∀ v, p v) :=
  decidable_of_iff (p .unknown ∧ p (.fixed false) ∧ p (.fixed true)) ⟨by
    intro h v
    cases v with
    | unknown => exact h.1
    | fixed v => cases v <;> first | exact h.2.1 | exact h.2.2,
    fun h => ⟨h _,h _,h _⟩⟩

instance (v : Value) (b : Bool) : Decidable (v.agrees b) := by
  cases v <;> unfold Value.agrees <;> infer_instance

def Value.literal : Value → Bool → Value
  | .unknown, _ => .unknown | .fixed a, b => .fixed (a == b)

def Value.conj : Value → Value → Value
  | .fixed false, _ | _, .fixed false => .fixed false
  | .fixed true, .fixed true => .fixed true
  | _, _ => .unknown

def Value.negate (v : Value) (inv : Bool) : Value := match v with
  | .unknown => .unknown | .fixed a => .fixed (a ^^ inv)

structure Step where
  a : Value
  b : Value
  wantA : Bool
  wantB : Bool
  flipped : Bool
  keepA : Bool
  keepB : Bool

def Step.out (s : Step) := ((s.a.literal s.wantA).conj (s.b.literal s.wantB)).negate s.flipped

theorem Step.semantic (s : Step) (x y : Bool) (hx : s.a.agrees x) (hy : s.b.agrees y) :
    s.out.agrees (((x == s.wantA) && (y == s.wantB)) ^^ s.flipped) := by
  rcases s with ⟨a,b,wa,wb,inv,ka,kb⟩
  revert a b wa wb inv ka kb x y
  decide

def Step.retired (s : Step) := (if s.keepA then 0 else s.a.known) + (if s.keepB then 0 else s.b.known)
def Step.killed (s : Step) := min 1 (s.a.known + s.b.known)

def Step.charge (s : Step) :=
  (if s.keepA then s.a.known else 0) + (if s.keepB then s.b.known else 0) +
  match s.a.literal s.wantA,s.b.literal s.wantB with
    | .fixed false,.unknown | .unknown,.fixed false => 1 | _,_ => 0

/-- A literal may be reused with either sign without charging a U2 binary gate. -/
inductive Folded where
  | constant (bit : Bool)
  | useA (want inverse : Bool)
  | useB (want inverse : Bool)
  deriving DecidableEq

def Folded.eval : Folded → Bool → Bool → Bool
  | .constant b, _, _ => b
  | .useA want inverse, a, _ => (a == want) ^^ inverse
  | .useB want inverse, _, b => (b == want) ^^ inverse

/-- Return the zero-binary-gate replacement for a gate trivialized by this restriction. -/
def Step.fold (s : Step) : Option Folded :=
  match s.a.literal s.wantA, s.b.literal s.wantB with
  | .fixed false, _ | _, .fixed false => some (.constant s.flipped)
  | .fixed true, .fixed true => some (.constant (!s.flipped))
  | .fixed true, .unknown => some (.useB s.wantB s.flipped)
  | .unknown, .fixed true => some (.useA s.wantA s.flipped)
  | .unknown, .unknown => none

theorem Step.fold_happens (s : Step) : s.fold.isSome = (s.killed == 1) := by
  rcases s with ⟨a,b,wa,wb,inv,ka,kb⟩
  revert a b wa wb inv ka kb
  decide

theorem Step.fold_correct (s : Step) (x y : Bool) (hx : s.a.agrees x) (hy : s.b.agrees y) :
    (s.fold.map (fun e => e.eval x y)).getD (((x == s.wantA) && (y == s.wantB)) ^^ s.flipped) =
      (((x == s.wantA) && (y == s.wantB)) ^^ s.flipped) := by
  rcases s with ⟨a,b,wa,wb,inv,ka,kb⟩
  revert a b wa wb inv ka kb x y
  decide

/-- The numerical debit used by the bit-plane and scalar exhaustive searches. -/
theorem Step.account (s : Step) : s.charge + s.retired = s.killed + s.out.known := by
  rcases s with ⟨a,b,wa,wb,inv,ka,kb⟩
  revert a b wa wb inv ka kb
  decide

def killed (steps : List Step) := (steps.map Step.killed).sum
def charged (steps : List Step) := (steps.map Step.charge).sum

/-- Cardinality of live wires known constant, before and after every gate. -/
inductive Trace : Nat → List Step → Nat → Prop where
  | nil (v) : Trace v [] v
  | cons {v w z s ss} (balance : v + s.out.known = w + s.retired) (tail : Trace w ss z) :
      Trace v (s :: ss) z

theorem Trace.account {v z ss} (tr : Trace v ss z) : v + charged ss = killed ss + z := by
  induction tr with
  | nil => simp [killed,charged]
  | @cons v w z s ss bal tail ih =>
    have hs := s.account
    simp only [killed, charged, List.map_cons, List.sum_cons] at *
    omega

/-- If a complete trace ends with no live constants and leaves at least L gates after
    simplification, no intermediate prefix may have initial constants + prefix debit + L > budget. -/
theorem prune {initial middle kFirst kLast L budget : Nat} {ss ts : List Step}
    (hp : Trace initial ss middle) (hs : Trace middle ts 0)
    (hpCount : kFirst = killed ss) (hsCount : kLast = killed ts)
    (survive : L + kFirst + kLast ≤ budget) : L + initial + charged ss ≤ budget := by
  have h₁ := hp.account
  have h₂ := hs.account
  omega

end PinPotential
