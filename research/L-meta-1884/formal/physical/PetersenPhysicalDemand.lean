import PetersenPhysicalCut
open PetersenSignedBridge PetersenFrontier PetersenFrontierSearch PetersenWordCost
open PetersenPhysicalWords PetersenPhysicalCut
namespace PetersenPhysicalDemand

/-- Positive/negative boundary-row pairs in the order of the ten raw primary
coordinates. At each pair, only the indicated coordinate may break monotonicity. -/
def probes : List (Fin 38 × Fin 38) :=
  [(0,7),(0,9),(1,7),(2,11),(4,9),(6,9),(8,7),(12,11),(19,10),(28,7)]

def forcing (x : BitVec 38) : Bool :=
  probes.any fun (i,j) =>
    target.getLsbD i.val && !target.getLsbD j.val &&
    input.all (fun a => a == x || (mask pivot a j).getLsbD i.val)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 2400000 in
theorem census : input.all forcing = true ∧ pivot ∈ input.toFinset ∧ input.toFinset.card = 10 := by
  decide

/-- On the 38 selected rows alone, every physically realizable accepting
frontier must read every original vertex. -/
theorem must_read {U m c} (sub : U ⊆ input.toFinset)
    (run : Trace (fun a b o => o ∉ input.toFinset ∧ WordGate pivot a b o) U m c {target}) :
    U = input.toFinset := by
  apply Finset.Subset.antisymm sub
  intro x hx
  by_contra missing
  have found := List.all_eq_true.mp census.1 x (List.mem_toFinset.mp hx)
  obtain ⟨⟨i,j⟩,_,hit⟩ := List.any_eq_true.mp found
  simp only [Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hit
  have all : ∀ a ∈ U, before pivot a i j := by
    intro a ha
    have chk := hit.2 a (List.mem_toFinset.mp (sub ha))
    have non : a ≠ x := fun eq => missing (eq ▸ ha)
    have bit := (Bool.or_eq_true_iff.mp chk).resolve_left (fun e => non (beq_iff_eq.mp e))
    exact (mask_spec pivot a i j).mp bit
  have ord := tail_before census.2.1 (to_tail run) i j all target (Finset.mem_singleton_self _)
  exact Bool.false_ne_true (hit.1.2.symm.trans (ord.1 hit.1.1))

/-- A physical circuit computing the original Petersen target yields a complete
ten-register trace on the 38-bit input boundary. This accounts for the initial
positive/negative x₀ signals as one reusable source. -/
theorem all_ten {k W} (src : Direct rails k W) (out : PetersenTarget ∈ W) :
    ∃ m ≤ k, ∃ c,
      Trace (fun a b o => o ∉ input.toFinset ∧ WordGate pivot a b o) input.toFinset m c {target} ∧
      m+1=10+c := by
  obtain ⟨U,hs,m,hm,c,tr,account⟩ := boundary_coverage src out
  have e := must_read hs tr
  subst U
  exact ⟨m,hm,c,tr,by simpa [census.2.2] using account⟩

#print axioms all_ten
end PetersenPhysicalDemand
