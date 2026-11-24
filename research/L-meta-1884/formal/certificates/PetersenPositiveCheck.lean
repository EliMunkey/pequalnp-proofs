import PetersenPositiveDominance
open PetersenPhysicalWords PetersenWordCost PetersenDominantPin PetersenFrontierSearch
namespace PetersenPositiveCheck
variable {u w : Nat}
abbrev Instr := Bool × Nat × Nat

def eval (W : List (BitVec u)) (ins : Instr) : BitVec u :=
  gate ins.1 (W.getD ins.2.1 0) (W.getD ins.2.2 0)

def replay (I : List (BitVec u)) (program : List Instr) :=
  program.foldl (fun W i => eval W i :: W) I

private theorem memGet {W : List (BitVec u)} (has : 0∈W) (i : Nat) : W.getD i 0 ∈ W := by
  by_cases h : i < W.length
  · rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : W.length ≤ i)] using has

private theorem inclusion (W : List (BitVec u)) (p : List Instr) : W ⊆ replay W p := by
  induction p generalizing W with
  | nil => exact fun _ h => h
  | cons i p ih =>
    intro x h
    exact ih (eval W i :: W) (List.mem_cons_of_mem _ h)

theorem builds (I : List (BitVec u)) (p : List Instr) (zero : 0∈I) :
    Positive I p.length (replay I p) := by
  have go {W : List (BitVec u)} {j} (pr : Positive I j W) (z : 0∈W) :
      ∀ pp : List Instr, Positive I (j+pp.length) (replay W pp) := by
    intro pp
    induction pp generalizing j W with
    | nil => simpa [replay] using pr
    | cons i rest ih =>
      have added := Positive.add i.1 pr (memGet z i.2.1) (memGet z i.2.2)
      have r := ih added (List.mem_cons_of_mem _ z)
      simpa [eval,replay,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using r
  simpa using go Positive.start zero p

def check (r : Fin u→Fin w) (I : List (BitVec u)) (K : Nat) (t : BitVec w) (p : List Instr)
    (L : List (BitVec w)) (fuel : Nat) : Bool :=
  let q := PetersenPackedPin.project r t
  !forced r q t && (L.all fun a => (replay I p).any fun v => betterB q (PetersenPackedPin.project r a) v) &&
    decide (p.length+fuel < K+1+(L.toFinset.filter (fun a => forced r q a)).card)

theorem sound (r : Fin u → Fin w) {t : BitVec w} {I : List (BitVec u)} {K : Nat}
    (small : PetersenPhysicalProjection.NoPhysical I (PetersenPackedPin.project r t) K)
    (cs : 0∈I ∧ ~~~0∈I) {p : List Instr} {L : List (BitVec w)} {fuel : Nat}
    (ok : check r I K t p L fuel = true) {m c} (le : m≤fuel) : ¬Tail Plain L.toFinset m c {t} := by
  obtain ⟨⟨hot,all⟩,num⟩ := Bool.and_eq_true_iff.mp ok |>.imp_left Bool.and_eq_true_iff.mp
  apply PetersenPositiveDominance.blocks r small (builds I p cs.1) ⟨inclusion I p cs.1,inclusion I p cs.2⟩ _
      (by simpa using hot) (of_decide_eq_true num) le
  intro a mem
  obtain ⟨v,hv,good⟩ := List.any_eq_true.mp (List.all_eq_true.mp all a (List.mem_toFinset.mp mem))
  exact ⟨v,hv,(better_spec ..).mp good⟩
#print axioms sound
end PetersenPositiveCheck
