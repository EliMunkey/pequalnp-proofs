import PetersenAntiOrbit
import PetersenEleven
import PetersenPhysicalOrbit
open PetersenAntichain PetersenEleven PetersenFrontier PetersenFrontierSearch PetersenWordCost PetersenPhysicalWords
open PetersenSignedBridge PetersenMonotoneFrontier PetersenFrontierSymmetry PetersenPhysicalRowGroup
namespace PetersenElevenAntichain

private theorem toTrace {w : Nat} {t : BitVec w} {I U S m c} (r : ATrace t I U m c S) :
    Trace (CleanGate t I) U m c S := by
  induction r with
  | start => exact .start
  | step _ ne fr _ g _ ih => exact .step ih ne fr g

abbrev B := BitVec 38
def state (v : B × Bool) : List B := v.1 :: (if v.2 then PetersenEleven.sources else input)
def negatives := (List.finRange 38).filter (fun i => !target.getLsbD i.val)

theorem normalized {k W} (pr : Direct rails k W) (out : PetersenTarget∈W) :
    ∃ flag : Bool, ∃ m≤k, ∃ c, ATail target PetersenEleven.sources.toFinset
      (if flag then PetersenEleven.sources else input).toFinset m c {target} := by
  obtain ⟨U,sub,m,hm,c,tr⟩ := PetersenAntichain.source row pr out (by rfl) PetersenEleven.hot PetersenEleven.sources.toFinset PetersenEleven.initOK
  have all := PetersenEleven.ten_needed sub (toTrace tr)
  by_cases h : ~~~pivot ∈ U
  · have eq : PetersenEleven.sources.toFinset = U := Finset.Subset.antisymm (by
      simp only [PetersenEleven.sources,List.toFinset_cons,Finset.insert_subset_iff]
      exact ⟨h,all⟩) sub
    rw [←eq] at tr
    exact ⟨true,m,hm,c,toATail tr⟩
  · have eq : input.toFinset = U := Finset.Subset.antisymm all (by
      intro a ha
      have hs := sub ha
      simp only [PetersenEleven.sources,List.toFinset_cons,Finset.mem_insert] at hs
      exact hs.resolve_left (fun e => h (e ▸ ha)))
    rw [←eq] at tr
    exact ⟨false,m,hm,c,toATail tr⟩

theorem src_map (s : Aut) : PetersenEleven.sources.toFinset.map (rowEmb s.row)=PetersenEleven.sources.toFinset := by
  have np : rowEmb s.row (~~~pivot) = ~~~pivot := by
    change act s.row (~~~pivot) = ~~~pivot
    rw [pivot_eq,act_not,pivot_act]
  simp only [PetersenEleven.sources,List.toFinset_cons,Finset.map_insert,np,initial_eq,PetersenPhysicalOrbit.mapInputs s]

theorem map_state (s : Aut) (v : B × Bool) : (state v).toFinset.map (rowEmb s.row) = (state (act s.row v.1,v.2)).toFinset := by
  rcases v with ⟨o,flag⟩
  cases flag <;> simp only [state,Bool.false_eq_true,ite_false,ite_true,List.toFinset_cons,Finset.map_insert]
  · rw [initial_eq,PetersenPhysicalOrbit.mapInputs]; rfl
  · rw [src_map]; rfl
end PetersenElevenAntichain
