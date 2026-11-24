import PetersenMonotoneFrontier
import PetersenPhysicalDemand
import PetersenDominantPin
open PetersenSignedBridge PetersenFrontier PetersenFrontierSearch PetersenWordCost
open PetersenPhysicalWords PetersenMonotoneFrontier PetersenDominantPin
namespace PetersenEleven

abbrev B := BitVec 38
def sources : List B := (~~~pivot)::input
abbrev G := CleanGate target sources.toFinset

private theorem initials : (rails.map table).all (fun a => a==0 || a == ~~~0 || sources.contains a) = true := by decide
theorem hot : target≠0 ∧ target ≠ ~~~0 := by decide
theorem initOK : ∀ a∈rails, Sim target sources.toFinset (pack (a ∘ row)) := by
  intro a ha
  have eval := List.all_eq_true.mp initials (table a) (List.mem_map.mpr ⟨a,ha,rfl⟩)
  have am : Avail sources.toFinset (table a) := by
    simp only [Bool.or_eq_true_iff,beq_iff_eq,List.contains_iff_mem] at eval
    rcases eval with (e|e)|e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (List.mem_toFinset.mpr e))
  exact ⟨table a,am,PetersenMonotoneFrontier.refl _ _⟩

def detects (x : B) : Bool :=
  PetersenPhysicalDemand.probes.any fun (i,j) =>
    target.getLsbD i.val && !target.getLsbD j.val &&
      sources.all (fun a => a == x || !a.getLsbD i.val || a.getLsbD j.val)

private theorem pivotal : input.all detects = true := by decide
private theorem ascending {i j : Fin 38} {U T m c}
    (r : Trace G U m c T) (h : ∀a∈U, a.getLsbD i.val=true → a.getLsbD j.val=true) :
    ∀a∈T, a.getLsbD i.val=true → a.getLsbD j.val=true := by
  induction r with
  | start => exact h
  | @step m c K a b o _ _ _ g ih =>
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl|hold
    · obtain ⟨op,rfl⟩ := g.1
      have aa := ih a (Finset.mem_insert_self ..)
      have bb := ih b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
      cases op
      · change (a &&& b).getLsbD i.val = true → (a &&& b).getLsbD j.val = true
        simp only [BitVec.getLsbD_and,Bool.and_eq_true]; tauto
      · change (a ||| b).getLsbD i.val = true → (a ||| b).getLsbD j.val = true
        simp only [BitVec.getLsbD_or,Bool.or_eq_true]; tauto
    · exact ih f (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hold))

theorem ten_needed {U m c} (sub : U⊆sources.toFinset) (r : Trace G U m c {target}) : input.toFinset ⊆ U := by
  intro x hx
  by_contra miss
  obtain ⟨⟨i,j⟩,_,found⟩ := List.any_eq_true.mp (List.all_eq_true.mp pivotal x (List.mem_toFinset.mp hx))
  obtain ⟨⟨hot,cold⟩,all⟩ := Bool.and_eq_true_iff.mp found |>.imp_left Bool.and_eq_true_iff.mp
  apply Bool.false_ne_true
  have b := ascending (i := i) (j := j) r (by
    intro a ha v
    have chk := List.all_eq_true.mp all a (List.mem_toFinset.mp (sub ha))
    have ne : a ≠ x := fun e => miss (e ▸ ha)
    change ((a == x || !a.getLsbD i.val) || a.getLsbD j.val) = true at chk
    simp only [beq_eq_false_iff_ne.mpr ne,v,Bool.not_true,Bool.false_or] at chk
    exact chk) target (Finset.mem_singleton_self _) hot
  rw [b] at cold
  exact cold

theorem normalized {k W} (src : Direct rails k W) (out : PetersenTarget ∈ W) :
    ∃ L, (L=input ∨ L=sources) ∧ ∃ m≤k, ∃ c, Tail G L.toFinset m c {target} ∧ m+1=L.toFinset.card+c := by
  obtain ⟨U,sub,m,hm,c,tr,acc⟩ := PetersenMonotoneFrontier.realize row src out (by rfl) hot sources.toFinset initOK
  have all := ten_needed sub tr
  by_cases neg : ~~~pivot∈U
  · have eq : sources.toFinset=U := Finset.Subset.antisymm (by
      simp only [sources,List.toFinset_cons,Finset.insert_subset_iff]
      exact ⟨neg,all⟩) sub
    exact ⟨sources,Or.inr rfl,m,hm,c,eq.symm ▸ to_tail tr,eq.symm ▸ acc⟩
  · have eq : input.toFinset=U := Finset.Subset.antisymm all (by
      intro a ha
      have hs := sub ha
      simp only [sources,List.toFinset_cons,Finset.mem_insert] at hs
      exact hs.resolve_left (fun e => neg (e ▸ ha)))
    exact ⟨input,Or.inl rfl,m,hm,c,eq.symm ▸ to_tail tr,eq.symm ▸ acc⟩
#print axioms normalized
end PetersenEleven
