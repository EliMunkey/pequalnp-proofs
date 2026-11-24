import PetersenFrontier
import PetersenSignalCut

open PetersenFrontier PetersenWordCost PetersenSignalCut

namespace PetersenShortPrefix
variable {w : Nat}
abbrev V (w : Nat) := BitVec w

/-- A forward view of the suffix of a backwards-sliced register trace. -/
inductive Tail (G : V w → V w → V w → Prop) : Finset (V w) → Nat → Finset (V w) → Prop where
  | done (S) : Tail G S 0 S
  | more {K a b o d Z} : a ≠ b → o ∉ insert a (insert b K) → G a b o →
      Tail G (insert o K) d Z → Tail G (insert a (insert b K)) (d+1) Z

private theorem append_tail {G : V w → V w → V w → Prop} {I X Z d e}
    (a : Tail G I d X) (b : Tail G X e Z) : Tail G I (d+e) Z := by
  induction a with
  | done => simpa using b
  | more ne fresh g _ ih =>
    have res := Tail.more ne fresh g (ih b)
    convert res using 1; omega

theorem from_trace {G : V w → V w → V w → Prop} {I S m c} (r : Trace G I m c S) :
    Tail G I m S := by
  induction r with
  | start => exact Tail.done _
  | step _ ne fresh g ih => exact append_tail ih (Tail.more ne fresh g (Tail.done _))

theorem tail_capacity {G : V w → V w → V w → Prop} {I Z m} (r : Tail G I m Z) :
    I.card ≤ Z.card+m := by
  induction r with
  | done => omega
  | @more K a b o d Z _ fresh _ tail ih =>
    have ho : o ∉ K := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rw [Finset.card_insert_of_notMem ho] at ih
    have ab := Finset.card_insert_le a (insert b K)
    have bk := Finset.card_insert_le b K
    omega

/-- A gate may inspect only its two input bits; no monotonicity assumption. -/
def Local (G : V w → V w → V w → Prop) : Prop :=
  ∀ a b o, G a b o → ∀ i j : Fin w,
    PetersenWordCost.read a i = PetersenWordCost.read a j →
    PetersenWordCost.read b i = PetersenWordCost.read b j →
    PetersenWordCost.read o i = PetersenWordCost.read o j

theorem determines {G : V w → V w → V w → Prop} (locality : Local G) {I Z m}
    (r : Tail G I m Z) : ∀ i j, Agree I i j → Agree Z i j := by
  induction r with
  | done => exact fun _ _ e => e
  | @more K a b o d Z _ _ hg _ ih =>
    intro i j eq
    apply ih i j
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl|hv
    · exact locality a b v hg i j (eq a (by simp)) (eq b (by simp))
    · exact eq v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv))

/-- Delete either, both, or neither operand from the live registers, then add the output. -/
def successor (L : List (V w)) (a b o : V w) (dA dB : Bool) : List (V w) :=
  o :: L.filter (fun v => !(dA && v == a || dB && v == b))

theorem choose_retire {K : Finset (V w)} {L : List (V w)} {a b : V w} (o : V w)
    (ha : a ≠ b) (h : L.toFinset = insert a (insert b K)) :
    (successor L a b o (decide (a ∉ K)) (decide (b ∉ K))).toFinset = insert o K := by
  classical
  ext v
  simp only [successor,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    List.mem_filter,Bool.not_eq_true',Bool.or_eq_false_iff,Bool.and_eq_false_iff,
    decide_eq_false_iff_not,not_not,beq_eq_false_iff_ne]
  have mem : v ∈ L ↔ v = a ∨ v = b ∨ v ∈ K := by
    rw [← List.mem_toFinset,h];simp
  rw [mem]
  by_cases va : v=a <;> by_cases vb : v=b <;> simp_all

/-- Compute all rows agreeing with row i on each live wire, restricted to target-positive rows. -/
def same (L : List (V w)) (t : V w) (i : Fin w) : V w :=
  L.foldl (fun mask v => mask &&& (if PetersenWordCost.read v i then v else ~~~v)) t

private theorem same_bit (L : List (V w)) (t : V w) (i j : Fin w) :
    PetersenWordCost.read (same L t i) j = true ↔ PetersenWordCost.read t j = true ∧
      (∀ v ∈ L, PetersenWordCost.read v i = PetersenWordCost.read v j) := by
  induction L generalizing t with
  | nil => simp [same]
  | cons a L ih =>
    change PetersenWordCost.read (same L (t &&& (if PetersenWordCost.read a i then a else ~~~a)) i) j = true ↔ _
    rw [ih]
    have gate (b : V w) : PetersenWordCost.read (t &&& b) j = (PetersenWordCost.read t j && PetersenWordCost.read b j) := by
      simp [PetersenWordCost.read]
    rw [gate]
    cases hi : PetersenWordCost.read a i <;> cases hj : PetersenWordCost.read a j <;>
      simp_all [PetersenWordCost.read,j.isLt]

def separates (L : List (V w)) (t : V w) (negatives : List (Fin w)) : Bool :=
  negatives.all fun i => PetersenWordCost.read t i || same L t i == 0

theorem separates_of_tail {G : V w → V w → V w → Prop} (locality : Local G)
    {I d} {t : V w} (r : Tail G I d {t}) (L : List (V w)) (hi : L.toFinset = I)
    (negatives : List (Fin w)) : separates L t negatives = true := by
  apply List.all_eq_true.mpr
  intro i _
  apply Bool.or_eq_true_iff.mpr
  cases bit : PetersenWordCost.read t i with
  | true => exact Or.inl rfl
  | false =>
    right
    apply beq_iff_eq.mpr
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let v : Fin w := ⟨j,hj⟩
    have ff : PetersenWordCost.read (same L t i) v = false := by
      cases h : PetersenWordCost.read (same L t i) v with
      | false => rfl
      | true =>
        obtain ⟨hot,agree⟩ := (same_bit L t i v).mp h
        have bad := determines locality r i v (fun x hx => agree x (List.mem_toFinset.mp (hi ▸ hx))) t (by simp)
        rw [bit,hot] at bad
        contradiction
    simpa [PetersenWordCost.read,v] using ff

def viable (L : List (V w)) (t : V w) (neg : List (Fin w)) (budget : Nat) : Bool :=
  decide (L.toFinset.card ≤ budget+1) && separates L t neg

/-- Bounded lookahead: reaching depth zero without closing a prefix returns false
(unresolved). Only the true result is used as a proof of impossibility. -/
def exclude (ops : V w → V w → List (V w)) (t : V w) (neg : List (Fin w)) :
    Nat → Nat → List (V w) → Bool
  | depth, fuel, L =>
    if !viable L t neg fuel then true else
    if L.contains t then false else
    match depth, fuel with
    | 0, _ => false
    | _, 0 => true
    | n+1,k+1 => L.all fun a => L.all fun b =>
        a == b || (ops a b).all fun o =>
          L.contains o || [false,true].all fun da => [false,true].all fun db =>
            exclude ops t neg n k (successor L a b o da db)


theorem exclude_sound {G : V w → V w → V w → Prop} (locality : Local G)
    (ops : V w → V w → List (V w)) (complete : ∀ a b o, G a b o → o ∈ ops a b)
    (t : V w) (neg : List (Fin w)) (depth : Nat) :
    ∀ {I m fuel} (L : List (V w)), L.toFinset = I → m ≤ fuel → Tail G I m {t} →
      exclude ops t neg depth fuel L ≠ true := by
  induction depth with
  | zero =>
    intro I m fuel L eq le r
    have cap := tail_capacity r
    have card : L.toFinset.card ≤ fuel+1 := by rw [eq];simp at cap;omega
    have good : viable L t neg fuel = true := Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true card,separates_of_tail locality r L eq neg⟩
    simp [exclude,good]
  | succ d ih =>
    intro I m fuel L eq le r bad
    have cap := tail_capacity r
    have card : L.toFinset.card ≤ fuel+1 := by rw [eq];simp at cap;omega
    have good : viable L t neg fuel = true := Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true card,separates_of_tail locality r L eq neg⟩
    by_cases done : t ∈ L
    · cases fuel <;> simp [exclude,good,done] at bad
    cases r with
    | done =>
      apply done
      apply List.mem_toFinset.mp
      rw [eq]
      simp
    | @more K a b o m Z ab fresh hg tail =>
      cases fuel with
      | zero => omega
      | succ k =>
        have step :
            (L.all fun a => L.all fun b =>
            a == b || (ops a b).all fun o =>
              L.contains o || [false,true].all fun da => [false,true].all fun db =>
                exclude ops t neg d k (successor L a b o da db)) = true := by
          simpa [exclude,good,done] using bad
        have ma : a ∈ L := List.mem_toFinset.mp (eq.symm ▸ (by simp : a ∈ insert a (insert b K)))
        have mb : b ∈ L := List.mem_toFinset.mp (eq.symm ▸ (by simp : b ∈ insert a (insert b K)))
        have be := List.all_eq_true.mp (List.all_eq_true.mp step a ma) b mb
        have different : (a==b) = false := beq_eq_false_iff_ne.mpr ab
        simp only [different,Bool.false_or] at be
        have oe := List.all_eq_true.mp be o (complete _ _ _ hg)
        have unused : o ∉ L := fun h => fresh (eq ▸ List.mem_toFinset.mpr h)
        simp only [List.contains_eq_mem,decide_eq_false unused,Bool.false_or] at oe
        have bm (v : Bool) : v ∈ [false,true] := by cases v <;> simp
        have fail := List.all_eq_true.mp (List.all_eq_true.mp oe (decide (a ∉ K)) (bm _)) (decide (b ∉ K)) (bm _)
        exact ih _ (choose_retire o ab eq) (by omega) tail fail

#print axioms exclude_sound
end PetersenShortPrefix
