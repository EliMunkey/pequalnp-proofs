import PetersenMinor

open PetersenSignedBridge PetersenFrontier PetersenTracePin

namespace PetersenPhysicalPin

variable {X Y : Type}
noncomputable local instance : DecidableEq (Func X) := Classical.decEq _
noncomputable local instance (r : Y → X) : DecidablePred (constant r) := Classical.decPred _

def represented (r : Y → X) (key : Func X → Func X) (V : List (Func Y)) (a : Func X) : Prop :=
  ∀ f, key f = a → f ∘ r ∈ V

private theorem contains {I S : List (Func Y)} {j} (run : Direct I j S) : ∀ f ∈ I, f ∈ S := by
  induction run with
  | start => exact fun _ h => h
  | and _ _ _ ih => exact fun f h => List.mem_cons_of_mem _ (ih f h)
  | or _ _ _ ih => exact fun f h => List.mem_cons_of_mem _ (ih f h)

private theorem sign_const (r : Y → X) {key : Func X → Func X} (sgn : ∀ f, negRelated (key f) f)
    {f} (h : constant r (key f)) : constant r f := by
  obtain ⟨v,hv⟩ := h
  rcases sgn f with eq|eq
  · exact ⟨v,eq ▸ hv⟩
  · refine ⟨!v,?_⟩
    rw [eq] at hv
    funext x
    have q := congrArg not (congrFun hv x)
    simpa [PetersenFrontier.flip,Function.comp_def] using q

private theorem fold_input {V : List (Func Y)} (o c : Bool) {a : Func Y} (h : a ∈ V)
    (cs : ∀ b : Bool, (fun _ => b) ∈ V) :
    PetersenFrontier.bin o (fun _ => c) a ∈ V ∧ PetersenFrontier.bin o a (fun _ => c) ∈ V := by
  cases o <;> cases c
  · constructor <;> convert cs false using 1 <;> (funext x; simp [bin])
  · constructor <;> convert h using 1 <;> (funext x; simp [bin])
  · constructor <;> convert h using 1 <;> (funext x; simp [bin])
  · constructor <;> convert cs true using 1 <;> (funext x; simp [bin])

private theorem propagate {I V : List (Func Y)} {a b o : Func X} {j} (r : Y → X)
    {key : Func X → Func X} (sgn : ∀ f, negRelated (key f) f)
    (apart : ∀ f g, key f = key g → f ≠ g → f ∘ r ∈ I)
    (cs : ∀ b : Bool, (fun _ => b) ∈ I) (g : keyedGate key a b o)
    (run : Direct I j V) (ha : represented r key V a) (hb : represented r key V b) :
    ∃ S, Direct I (j + debit (constant r) a b) S ∧ represented r key S o ∧ V ⊆ S := by
  obtain ⟨u,v,op,hu,hv,ho,_⟩ := g
  have au := ha u hu
  have bv := hb v hv
  let f := bin op (u ∘ r) (v ∘ r)
  have extend {l S} (rs : Direct I l S) (sup : V ⊆ S) (mem : f ∈ S) :
      ∃ S, Direct I l S ∧ represented r key S o ∧ V ⊆ S := by
    refine ⟨S,rs,?_,sup⟩
    intro z hz
    by_cases same : z = bin op u v
    · exact same ▸ mem
    · exact contains rs _ (apart z _ (hz.trans ho.symm) same)
  by_cases h : constant r a ∨ constant r b
  · simp only [debit,ite_eq_left h,Nat.add_zero]
    apply extend run (fun _ h => h)
    have cs' := fun x => contains run _ (cs x)
    rcases h with ca | cb
    · obtain ⟨c,hc⟩ := sign_const r sgn (hu.symm ▸ ca)
      change bin op (u ∘ r) (v ∘ r) ∈ V
      rw [hc]
      exact (fold_input op c bv cs').1
    · obtain ⟨c,hc⟩ := sign_const r sgn (hv.symm ▸ cb)
      change bin op (u ∘ r) (v ∘ r) ∈ V
      rw [hc]
      exact (fold_input op c au cs').2
  · simp only [debit,ite_eq_right h]
    apply extend (S := f :: V) _ (fun _ h => List.mem_cons_of_mem _ h) (List.mem_cons_self ..)
    cases op <;> first | exact Direct.and run au bv | exact Direct.or run au bv

/-- Physical restrictions produce an actual AND/OR circuit. Every alias caused by
    making the two distinguished primary rails share a key must be present in the restricted
    input supply. Intermediate gates receive only their physical polarities. -/
theorem restrict_frontier {start stop : Finset (Func X)} {m c q : Nat} {I V : List (Func Y)}
    (r : Y → X) {key : Func X → Func X} (sgn : ∀ f, negRelated (key f) f)
    (apart : ∀ f g, key f = key g → f ≠ g → f ∘ r ∈ I)
    (cs : ∀ b : Bool, (fun _ => b) ∈ I)
    (t : Trace (keyedGate key) start m c stop) (pre : Direct I q V)
    (base : ∀ f ∈ start, represented r key V f) :
    ∃ j S, Direct I j S ∧ (∀ f ∈ stop, represented r key S f) ∧
      j + (start.filter (constant r)).card ≤ q + m + (stop.filter (constant r)).card := by
  induction t with
  | start => exact ⟨q,V,pre,base,by omega⟩
  | @step m c K a b o _ distinct fresh g ih =>
    obtain ⟨j,S,rj,cover,bound⟩ := ih
    obtain ⟨S',rj',ho,old⟩ := propagate r sgn apart cs g rj
      (cover a (Finset.mem_insert_self ..)) (cover b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..)))
    have step := step_budget (constant r) distinct fresh (constant_gate r (PetersenMinor.keyedSigned _ sgn g))
    refine ⟨_,S',rj',?_,by omega⟩
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl|hk
    · exact ho
    · exact fun v h => old (cover _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hk)) _ h)

theorem physical_alias {I : List (Func Y)} (r : Y → PInput)
    (positive : vertex 0 ∘ r ∈ I) (negative : negZero ∘ r ∈ I) (f g : Func PInput)
    (eq : physicalKey f = physicalKey g) (ne : f ≠ g) : f ∘ r ∈ I := by
  by_cases hf : f = negZero
  · exact hf ▸ negative
  · by_cases hg : g = negZero
    · simp only [physicalKey,hf,hg,ite_false,ite_true] at eq
      exact eq ▸ positive
    · simp only [physicalKey,hf,hg,ite_false] at eq
      exact (ne eq).elim

end PetersenPhysicalPin
