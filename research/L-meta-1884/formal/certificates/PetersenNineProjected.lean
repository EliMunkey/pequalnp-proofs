import PetersenNineOrbit
import PetersenPhysicalProjection

open PetersenPhysicalWords PetersenMonotoneFrontier PetersenNineData PetersenNinePositive
open PetersenFrontier PetersenFrontierSearch
namespace PetersenNineProjected

def basis : List PetersenNineData.B := 0 :: (~~~0) :: sources

/-- The eight outstanding nine-vertex continuations also bound arbitrary
AND/OR programs on the 24 boundary rows, including access to both constants. -/
theorem small {k : Nat}
    (suffix : ∀ o ∈ PetersenNineOrbit.outputs, PetersenNinePositive.Blocked k (o :: sources)) :
    PetersenPhysicalProjection.NoPhysical basis label (k+1) := by
  intro n le S prog out
  have base (a) (ha : a ∈ basis) : Sim label sources.toFinset a := by
    refine ⟨a,?_,PetersenMonotoneFrontier.refl _ _⟩
    simp only [basis,List.mem_cons] at ha
    exact ha.imp_right (fun h => h.imp_right List.mem_toFinset.mpr)
  obtain ⟨m,hm,W,pref,_,cov⟩ := normalize prog label sources.toFinset base
  obtain ⟨v,hv,he⟩ := cov label out
  have ve := sink he
  subst v
  have live : label ∈ W := (hv.resolve_left demanded.2.1).resolve_left demanded.2.2.1
  obtain ⟨U,sub,q,hq,c,tr⟩ := pref.schedule {label} (Finset.singleton_subset_iff.mpr live)
  have run := to_tail tr
  have eq := include_all sub (tailGate (fun _ _ _ g => clean_physical g) run)
  exact PetersenNineOrbit.eight suffix (by omega) (eq ▸ run)
#print axioms small
end PetersenNineProjected
