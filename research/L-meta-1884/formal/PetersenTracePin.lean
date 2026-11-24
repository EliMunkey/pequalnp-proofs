import PetersenFrontier
import PetersenCofactor

open PetersenSignedBridge PetersenFrontier

namespace PetersenTracePin

section Accounting
variable {α : Type} [DecidableEq α] (p : α → Prop) [DecidablePred p]

def debit (a b : α) : Nat := if p a ∨ p b then 0 else 1

theorem step_budget {K : Finset α} {a b o : α} (distinct : a ≠ b)
    (fresh : o ∉ insert a (insert b K)) (both : p a → p b → p o) :
    debit p a b + ((insert a (insert b K)).filter p).card ≤ 1 + ((insert o K).filter p).card := by
  have out : o ∉ K := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  by_cases pa : p a <;> by_cases pb : p b <;> by_cases po : p o <;>
    by_cases ka : a ∈ K <;> by_cases kb : b ∈ K <;>
    simp_all [debit, Finset.filter_insert, Finset.card_insert_of_notMem, Finset.mem_filter] <;> omega

end Accounting

variable {X Y : Type}
noncomputable local instance : DecidableEq (Func X) := Classical.decEq _

def signed (s : Bool) (f : Func X) : Func X := fun x => if s then !(f x) else f x

def gate (a b o : Func X) : Prop :=
  ∃ op sa sb so, o = signed so (PetersenCofactor.applyGate op (signed sa a) (signed sb b))

def constant (r : Y → X) (f : Func X) : Prop := ∃ v : Bool, f ∘ r = fun _ => v
noncomputable local instance (r : Y → X) : DecidablePred (constant r) := Classical.decPred _

private theorem avSigned {W : List (Func Y)} {a : Func Y} (s : Bool) (h : Av W a) :
    Av W (signed s a) := by cases s <;> first | exact h | exact Av.neg h

private theorem composeSigned (r : Y → X) (s : Bool) (f : Func X) :
    signed s f ∘ r = signed s (f ∘ r) := rfl

theorem constant_gate {a b o : Func X} (r : Y → X) (g : gate a b o)
    (ha : constant r a) (hb : constant r b) : constant r o := by
  obtain ⟨op,sa,sb,so,rfl⟩ := g
  obtain ⟨v,hv⟩ := ha
  obtain ⟨w,hw⟩ := hb
  refine ⟨(signed so (PetersenCofactor.applyGate op (signed sa (fun _ : Unit => v))
       (signed sb (fun _ : Unit => w)))) (),?_⟩
  funext x
  have a' := congrFun hv x
  have b' := congrFun hw x
  simpa [signed,PetersenCofactor.applyGate,Function.comp_def] using
    congrArg₂ (fun aa bb => if so then !(if op then (if sa then !aa else aa) || (if sb then !bb else bb)
      else (if sa then !aa else aa) && (if sb then !bb else bb)) else
      (if op then (if sa then !aa else aa) || (if sb then !bb else bb)
      else (if sa then !aa else aa) && (if sb then !bb else bb))) a' b'

private theorem weaken {V : List (Func Y)} {a d : Func Y} (h : Av V a) : Av (d::V) a := by
  induction h with
  | wire h => exact Av.wire (List.mem_cons_of_mem _ h)
  | zero => exact Av.zero
  | one => exact Av.one
  | neg _ ih => exact Av.neg ih

private theorem constant_input {V : List (Func Y)} (o c : Bool) {a : Func Y} (h : Av V a) :
    Av V (PetersenCofactor.applyGate o (fun _ => c) a) ∧
    Av V (PetersenCofactor.applyGate o a (fun _ => c)) := by
  cases o <;> cases c
  · constructor <;> convert (Av.zero (W := V)) using 1 <;> (funext x; simp [PetersenCofactor.applyGate])
  · constructor <;> convert h using 1 <;> (funext x; simp [PetersenCofactor.applyGate])
  · constructor <;> convert h using 1 <;> (funext x; simp [PetersenCofactor.applyGate])
  · constructor <;> convert (Av.one (W := V)) using 1 <;> (funext x; simp [PetersenCofactor.applyGate])

private theorem fold_or_pay {I V : List (Func Y)} {a b o : Func X} {j : Nat}
    (r : Y → X) (g : gate a b o) (run : Run I j V) (ha : Av V (a ∘ r)) (hb : Av V (b ∘ r)) :
    ∃ S, Run I (j + debit (constant r) a b) S ∧ Av S (o ∘ r) ∧ (∀ f, Av V f → Av S f) := by
  obtain ⟨op,sa,sb,so,rfl⟩ := g
  let u := signed sa (a ∘ r)
  let v := signed sb (b ∘ r)
  let f := PetersenCofactor.applyGate op u v
  have au := avSigned sa ha
  have bv := avSigned sb hb
  by_cases h : constant r a ∨ constant r b
  · simp only [debit,ite_eq_left h,Nat.add_zero]
    refine ⟨V,run,avSigned so ?_,fun _ h => h⟩
    change Av V (PetersenCofactor.applyGate op (signed sa (a ∘ r)) (signed sb (b ∘ r)))
    rcases h with ⟨c,hc⟩ | ⟨c,hc⟩
    · rw [hc]
      exact (constant_input op (if sa then !c else c) bv).1
    · rw [hc]
      exact (constant_input op (if sb then !c else c) au).2
  · simp only [debit,ite_eq_right h]
    refine ⟨f::V,?_,avSigned so (Av.wire (List.mem_cons_self ..)),fun _ h => weaken h⟩
    cases op <;> first | exact Run.and run au bv | exact Run.or run au bv

/-- Constant propagation along a last-use trace constructs an actual signed circuit for the
    restricted live signals and subtracts every distinct constant present at the initial frontier,
    provided the last frontier has no constant rails. -/
theorem restrict_frontier {start stop : Finset (Func X)} {m c q : Nat}
    {I V : List (Func Y)} (r : Y → X) (t : Trace gate start m c stop) (pre : Run I q V)
    (base : ∀ f ∈ start, Av V (f ∘ r)) :
    ∃ j S, Run I j S ∧ (∀ f ∈ stop, Av S (f ∘ r)) ∧
      j + (start.filter (constant r)).card ≤ q + m + (stop.filter (constant r)).card := by
  induction t with
  | start => exact ⟨q,V,pre,base,by omega⟩
  | @step m c K a b o _ distinct fresh g ih =>
    obtain ⟨j,S,rj,cover,bound⟩ := ih
    obtain ⟨S',rj',ho,old⟩ := fold_or_pay r g rj
      (cover a (Finset.mem_insert_self ..)) (cover b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..)))
    have step := step_budget (constant r) distinct fresh (constant_gate r g)
    refine ⟨_,S',rj',?_,by omega⟩
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hk
    · exact ho
    · exact old _ (cover _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hk)))

theorem prune_suffix {start : Finset (Func X)} {o : Func X} {m c q lower : Nat}
    {I V : List (Func Y)} (r : Y → X) (t : Trace gate start m c {o}) (pre : Run I q V)
    (base : ∀ f ∈ start, Av V (f ∘ r)) (nonconst : ¬ constant r o)
    (lb : ∀ j W, Run I j W → Av W (o ∘ r) → lower ≤ j) :
    lower + (start.filter (constant r)).card ≤ q + m := by
  obtain ⟨j,S,rj,cover,h⟩ := restrict_frontier r t pre base
  have := lb j S rj (cover o (Finset.mem_singleton_self _))
  have empty : ({o} : Finset (Func X)).filter (constant r) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hz,hconst⟩ := Finset.mem_filter.mp hz
    have eq := Finset.mem_singleton.mp hz
    exact nonconst (eq ▸ hconst)
  rw [empty,Finset.card_empty,Nat.add_zero] at h
  exact (Nat.le_trans (Nat.add_le_add_right this _) h)

end PetersenTracePin
