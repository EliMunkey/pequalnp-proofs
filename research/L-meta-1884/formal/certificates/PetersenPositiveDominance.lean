import PetersenEleven
import PetersenPhysicalProjection
open PetersenFrontier PetersenFrontierSearch PetersenWordCost PetersenPhysicalWords
open PetersenDominantPin PetersenMonotoneFrontier
namespace PetersenPositiveDominance
variable {u w : Nat}

def Good (r : Fin u → Fin w) (t : BitVec u) (W : List (BitVec u)) (a : BitVec w) :=
  ∃ b∈W, Better t (PetersenPackedPin.project r a) b

private theorem choose_const {V : List (BitVec u)} (cs : 0∈V ∧ ~~~0∈V) (b : Bool) : constWord b ∈ V := by
  cases b <;> first | exact cs.1 | exact cs.2

private theorem folding {V : List (BitVec u)} (cs : 0∈V ∧ ~~~0∈V) (op v : Bool) {y : BitVec u} (h : y∈V) :
    gate op (constWord v) y ∈ V ∧ gate op y (constWord v) ∈ V := by
  cases op <;> cases v <;> simp_all [gate,constWord]

private theorem closedConst (r : Fin u→Fin w) (t : BitVec u) {a b o} (g : Plain a b o)
    (ca : forced r t a) (cb : forced r t b) : forced r t o := by
  obtain ⟨op,rfl⟩ := g
  obtain ⟨va,ha⟩ := (forced_iff ..).mp ca
  obtain ⟨vb,hb⟩ := (forced_iff ..).mp cb
  apply (forced_iff ..).mpr
  refine ⟨if op then va||vb else va&&vb,?_⟩
  rw [projectGate]
  have eq : gate op (constWord va : BitVec u) (constWord vb) =
      constWord (if op then va||vb else va&&vb) := by cases op <;> cases va <;> cases vb <;> simp [gate,constWord]
  rw [←eq]
  exact move op ha hb

theorem advance (r : Fin u → Fin w) (t : BitVec u) {a b o : BitVec w} (g : Plain a b o)
    {I V : List (BitVec u)} {q} (pre : Positive I q V) (cs : 0∈V ∧ ~~~0∈V)
    (ax : Good r t V a) (byy : Good r t V b) :
    ∃ S, Positive I (q+PetersenTracePin.debit (fun v => forced r t v=true) a b) S ∧
      Good r t S o ∧ V ⊆ S := by
  obtain ⟨op,rfl⟩ := g
  obtain ⟨x,hx,bx⟩ := ax
  obtain ⟨y,hy,byy⟩ := byy
  by_cases can : forced r t a=true ∨ forced r t b=true
  · simp only [PetersenTracePin.debit,ite_eq_left can,Nat.add_zero]
    refine ⟨V,pre,?_,fun _ h => h⟩
    rcases can with ha|hb
    · obtain ⟨z,hz⟩ := (forced_iff ..).mp ha
      exact ⟨_,(folding cs op z hy).1,projectGate r op a b ▸ move op hz byy⟩
    · obtain ⟨z,hz⟩ := (forced_iff ..).mp hb
      exact ⟨_,(folding cs op z hx).2,projectGate r op a b ▸ move op bx hz⟩
  · simp only [PetersenTracePin.debit,ite_eq_right can]
    refine ⟨_,Positive.add op pre hx hy,⟨_,List.mem_cons_self ..,projectGate r op a b ▸ move op bx byy⟩,?_⟩
    exact fun _ h => List.mem_cons_of_mem _ h

theorem restrict (r : Fin u → Fin w) (t : BitVec u) {A T m c} (tail : Tail Plain A m c T)
    {I V : List (BitVec u)} {q} (pre : Positive I q V) (cs : 0∈V ∧ ~~~0∈V)
    (covered : ∀ a∈A, Good r t V a) :
    ∃ j S, Positive I j S ∧ (∀ a∈T, Good r t S a) ∧
      j + (A.filter (fun a => forced r t a)).card ≤ q + m + (T.filter (fun a => forced r t a)).card := by
  induction tail generalizing q V with
  | nil => exact ⟨q,V,pre,covered,by omega⟩
  | @step K a b o m c T ne fresh gate _ ih =>
    obtain ⟨S,prog,cv,sub⟩ := advance r t gate pre cs (covered a (Finset.mem_insert_self ..))
      (covered b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..)))
    have cost := PetersenTracePin.step_budget (fun a => forced r t a=true) ne fresh (closedConst r t gate)
    obtain ⟨j,Z,pr,finish,lb⟩ := ih prog ⟨sub cs.1,sub cs.2⟩ (by
      intro a mem
      rcases Finset.mem_insert.mp mem with rfl|hold
      · exact cv
      · obtain ⟨v,hv,good⟩ := covered a (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hold))
        exact ⟨v,sub hv,good⟩)
    exact ⟨j,Z,pr,finish,by omega⟩

theorem blocks (r : Fin u → Fin w) {t : BitVec w} {I V : List (BitVec u)} {K q fuel}
    (small : PetersenPhysicalProjection.NoPhysical I (PetersenPackedPin.project r t) K)
    (pre : Positive I q V) (cs : 0∈V ∧ ~~~0∈V) {L : Finset (BitVec w)}
    (cover : ∀ a∈L, Good r (PetersenPackedPin.project r t) V a)
    (hot : forced r (PetersenPackedPin.project r t) t = false)
    (fail : q+fuel < K+1+(L.filter (fun a => forced r (PetersenPackedPin.project r t) a)).card)
    {m c} (hm : m≤fuel) : ¬Tail Plain L m c {t} := by
  intro tail
  obtain ⟨j,S,pr,finish,bd⟩ := restrict r _ tail pre cs cover
  obtain ⟨v,hv,eq⟩ := finish t (Finset.mem_singleton_self _)
  have mem := sink eq ▸ hv
  have z : (({t} : Finset _).filter (fun a => forced r (PetersenPackedPin.project r t) a)).card=0 := by simp [hot]
  rw [z,Nat.add_zero] at bd
  exact small j (by omega) S pr mem
#print axioms blocks
end PetersenPositiveDominance
