import PetersenNineData
import PetersenPhysicalCut
import PetersenPhysicalSearch
open PetersenSignedBridge PetersenFrontier PetersenFrontierSearch PetersenWordCost
open PetersenMonotoneFrontier PetersenNineData PetersenPhysicalWords PetersenPhysicalCut
open PetersenFrontierSymmetry
namespace PetersenNinePositive
abbrev P := PetersenPhysicalSearch.Allowed (0::sources).toFinset (0:PetersenNineData.B)
abbrev C := CleanGate label sources.toFinset
abbrev Blocked := PetersenPhysicalSearch.Blocked (0::sources) (0:PetersenNineData.B) label

theorem tailGate {α : Type*} [DecidableEq α] {F H : α→α→α→Prop} {S T m c}
    (h : ∀a b o, F a b o → H a b o) (s : Tail F S m c T) : Tail H S m c T := by
  induction s with
  | nil => exact .nil _
  | step n fr g _ ih => exact .step n fr (h _ _ _ g) ih

private theorem rowLit (x : PetersenNineData.B) : x∈literals 0 x := by
  unfold literals; split
  · rename_i e; rw [e]; exact List.mem_cons_self ..
  · exact List.mem_cons_self ..

theorem clean_physical {a b o : PetersenNineData.B} (g : C a b o) : P a b o := by
  have notInp : ¬Avail sources.toFinset o := fun h => g.2 o h (PetersenMonotoneFrontier.refl label _)
  have key0 : PetersenPhysicalWords.key 0 o = o := by rw [PetersenPhysicalWords.key,ite_eq_right (fun eq => notInp (Or.inr (Or.inl eq)))]
  refine ⟨?_,?_⟩
  · intro h; simp only [List.toFinset_cons,Finset.mem_insert] at h
    exact notInp (h.imp_right (fun v => Or.inr v))
  · obtain ⟨op,eq⟩:=g.1
    apply List.mem_flatMap.mpr
    refine ⟨(a,b),List.mem_product.mpr ⟨rowLit a,rowLit b⟩,?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    cases op
    · left; change o=a&&&b at eq; rw [←eq,key0]
    · right; change o=a|||b at eq; rw [←eq,key0]

theorem init_ok (a : (V→Bool)→Bool) (mem : a∈PetersenNineData.raw) : Sim label sources.toFinset (pack (a ∘ PetersenNineData.row)) := by
  simp only [PetersenNineData.raw,List.mem_cons,List.mem_ofFn] at mem
  rcases mem with rfl|rfl|⟨i,rfl⟩
  · have e : pack ((fun _ : V→Bool => false) ∘ PetersenNineData.row)=0 := by decide
    rw [e]; exact ⟨0,Or.inl rfl,PetersenMonotoneFrontier.refl label _⟩
  · have e : pack ((fun _ : V→Bool => true) ∘ PetersenNineData.row) = ~~~0 := by decide
    rw [e]; exact ⟨_,Or.inr (Or.inl rfl),PetersenMonotoneFrontier.refl label _⟩
  · rw [primary_ok]; refine ⟨_,Or.inr (Or.inr ?_),PetersenMonotoneFrontier.refl label _⟩
    exact List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩)

def negatives : List R := (List.finRange 24).filter (fun j => !label.getLsbD j.val)
def needed (v : PetersenNineData.B) : Bool := !fits 0 label negatives (sources.filter (· != v))
set_option maxRecDepth 12000 in
theorem demanded : sources.all needed=true ∧ label≠0 ∧ label ≠ ~~~0 ∧ label∉sources.toFinset := by decide

theorem include_all {U m c} (sub : U⊆sources.toFinset) (r : Tail P U m c {label}) : U=sources.toFinset := by
  apply Finset.Subset.antisymm sub
  intro a ha
  by_contra missing
  have ex := List.all_eq_true.mp demanded.1 a (List.mem_toFinset.mp ha)
  change (!fits 0 label negatives (sources.filter (· != a)))=true at ex
  have supplies (i j : R) (all : ∀v∈sources.filter (· != a), before 0 v i j) : ∀v∈U,before 0 v i j := by
    intro v h; apply all; apply List.mem_filter.mpr
    exact ⟨List.mem_toFinset.mp (sub h),bne_iff_ne.mpr (fun eq => missing (eq ▸ h))⟩
  have hp : (0:PetersenNineData.B)∈(0::sources).toFinset := by simp
  have yes : fits 0 label negatives (sources.filter (·!=a))=true := by
    apply List.all_eq_true.mpr
    intro j _
    apply Bool.or_eq_true_iff.mpr
    cases hj : label.getLsbD j.val with
    | true => exact Or.inl rfl
    | false =>
      right; apply beq_iff_eq.mpr; by_contra nz
      obtain ⟨i,hi⟩ := nonzero_witness nz
      obtain ⟨pos,good⟩ := (compatible_spec ..).mp hi
      have ord := tail_before hp r i j (supplies i j good) label (Finset.mem_singleton_self _)
      exact Bool.false_ne_true (hj.symm.trans (ord.1 pos))
  simp only [yes,Bool.not_true,Bool.false_eq_true] at ex

theorem normalized {k W} (src : Direct PetersenNineData.raw k W) (out : PetersenNineData.target∈W) :
    ∃ m≤k,∃c,Tail C sources.toFinset m c {label} := by
  obtain ⟨U,sub,m,hm,c,r,_⟩ := PetersenMonotoneFrontier.realize PetersenNineData.row src out target_ok
    ⟨demanded.2.1,demanded.2.2.1⟩ sources.toFinset init_ok
  have tail:=to_tail r
  have eq:=include_all sub (tailGate (fun _ _ _ g => clean_physical g) tail)
  exact ⟨m,hm,c,eq ▸ tail⟩

#print axioms normalized
end PetersenNinePositive
