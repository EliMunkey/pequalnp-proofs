import PetersenAntichain
import PetersenFrontierSymmetry
open PetersenAntichain PetersenFrontierSymmetry PetersenMonotoneFrontier PetersenFrontier PetersenWordCost
namespace PetersenAntiSymmetry
variable {w : Nat} (p : Fin w ≃ Fin w)
local notation "B" => BitVec w

theorem ord {t a b : B} : Better (act p t) (act p a) (act p b) ↔ Better t a b := by
  simp only [Better,read_act,Function.comp_apply]
  exact ⟨fun h j=>by simpa only [Equiv.apply_symm_apply] using h (p.symm j),fun h j=>h (p j)⟩

theorem anti {t : B} {S : Finset B} (h : Anti t S) : Anti (act p t) (S.map (rowEmb p)) := by
  intro x hx y hy b
  obtain ⟨v,hv,rfl⟩:=Finset.mem_map.mp hx
  obtain ⟨z,hz,rfl⟩:=Finset.mem_map.mp hy
  exact congrArg _ (h v hv z hz ((ord p).mp b))

theorem clean {t a b o : B} {I : Finset B} (g : CleanGate t I a b o) :
    CleanGate (act p t) (I.map (rowEmb p)) (act p a) (act p b) (act p o) := by
  refine ⟨?_,?_⟩
  · obtain ⟨op,rfl⟩:=g.1; refine ⟨op,?_⟩
    cases op with
    | false => exact act_and p a b
    | true => exact act_or p a b
  · intro v hv good
    have orig (x : B) (av : Avail I x) (e : act p x=v) : False := by
      rw [←e] at good; exact g.2 x av ((ord p).mp good)
    rcases hv with q|q|q
    · exact orig 0 (Or.inl rfl) ((act_zero ..).trans q.symm)
    · exact orig _ (Or.inr (Or.inl rfl)) (by rw [act_not,act_zero,q])
    · obtain ⟨x,hx,rfl⟩:=Finset.mem_map.mp q
      exact orig _ (Or.inr (Or.inr hx)) rfl

theorem map {t : B} {I U m c T} (r : ATail t I U m c T) :
    ATail (act p t) (I.map (rowEmb p)) (U.map (rowEmb p)) m c (T.map (rowEmb p)) := by
  let e:=rowEmb p
  induction r with
  | nil _ h => exact .nil _ (anti p h)
  | @step K a b o m c T inc ne fresh no g _ ih =>
    change ATail _ _ ((insert a (insert b K)).map e) _ _ _
    have old : ((insert a (insert b K)).map e)=insert (e a) (insert (e b) (K.map e)) := by simp
    have orig := old ▸ anti p inc
    have fresh' : e o∉insert (e a) (insert (e b) (K.map e)) := by rw [←old];simpa using fresh
    have no' : ∀v∈insert (e a) (insert (e b) (K.map e)),¬Better (act p t) (e o) v := by
      intro v hv h;rw [←old] at hv;obtain ⟨x,hx,rfl⟩:=Finset.mem_map.mp hv
      exact no x hx ((ord p).mp h)
    have cr : credit (e a) (e b) (K.map e) = credit a b K := by simp [credit]
    rw [old,←cr]
    apply ATail.step orig (fun x=>ne (e.injective x)) fresh' no' (clean p g)
    simpa only [Finset.map_insert] using ih

#print axioms map
end PetersenAntiSymmetry
