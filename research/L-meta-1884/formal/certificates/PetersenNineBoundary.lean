import PetersenNineLift
import PetersenNineProjected
import PetersenMonotoneSample
open PetersenSignedBridge PetersenPhysicalWords PetersenWordCost PetersenMonotoneSample
namespace PetersenNineBoundary
set_option maxHeartbeats 0
set_option maxRecDepth 140000
set_option exponentiation.threshold 2048
abbrev X := Fin 512
abbrev R := Fin 24
def rows (i : R) : X := (#[6,132,160,3,33,66,100,69,12,138,104,201,144,52,80,58,25,386,288,385,320,264,274,277] : Array X)[i.val]?.getD 0
def vertex (i : Fin 9) : Fin 9 := (#[1,2,7,5,0,6,3,4,8] : Array (Fin 9))[i.val]?.getD 0
def anchor (i : X) : R := (#[6,7,9,3,6,7,0,0,9,11,9,3,8,8,0,0,13,16,15,3,13,23,0,0,15,16,15,3,8,8,0,0,6,4,15,3,6,4,0,0,10,4,15,3,8,4,0,0,13,4,15,3,13,4,0,0,15,4,15,3,8,4,0,0,6,7,5,3,6,7,0,0,10,11,5,3,8,8,0,0,14,14,5,3,14,14,0,0,14,14,5,3,8,8,0,0,6,4,5,3,6,4,0,0,10,4,5,3,8,4,0,0,14,4,5,3,14,4,0,0,14,4,5,3,8,4,0,0,9,11,9,3,1,1,0,0,9,11,9,3,1,1,0,0,12,12,12,3,1,1,0,0,12,12,12,3,1,1,0,0,2,2,2,2,1,1,0,0,2,2,2,2,1,1,0,0,2,2,2,2,1,1,0,0,2,2,2,2,1,1,0,0,11,11,5,3,1,1,0,0,11,11,5,3,1,1,0,0,12,12,5,3,1,1,0,0,12,12,5,3,1,1,0,0,2,2,2,2,1,1,0,0,2,2,2,2,1,1,0,0,2,2,2,2,1,1,0,0,2,2,2,2,1,1,0,0,17,19,17,3,23,23,0,0,21,21,21,3,8,8,0,0,22,23,22,3,23,23,0,0,21,21,21,3,8,8,0,0,18,4,18,3,18,4,0,0,18,4,18,3,8,4,0,0,18,4,18,3,18,4,0,0,18,4,18,3,8,4,0,0,20,20,5,3,20,20,0,0,20,20,5,3,8,8,0,0,14,14,5,3,14,14,0,0,14,14,5,3,8,8,0,0,18,4,5,3,18,4,0,0,18,4,5,3,8,4,0,0,14,4,5,3,14,4,0,0,14,4,5,3,8,4,0,0,17,19,17,3,1,1,0,0,21,21,21,3,1,1,0,0,12,12,12,3,1,1,0,0,12,12,12,3,1,1,0,0,2,2,2,2,1,1,0,0,2,2,2,2,1,1,0,0,2,2,2,2,1,1,0,0,2,2,2,2,1,1,0,0,20,20,5,3,1,1,0,0,20,20,5,3,1,1,0,0,12,12,5,3,1,1,0,0,12,12,5,3,1,1,0,0,2,2,2,2,1,1,0,0,2,2,2,2,1,1,0,0,2,2,2,2,1,1,0,0,2,2,2,2,1,1,0,0] : Array R)[i.val]?.getD 0
def below (x y : X) := x.val &&& y.val = x.val
instance (x y : X) : Decidable (below x y) := inferInstanceAs (Decidable (_ = _))
private theorem row_word : ∀ (i : Fin 9) (j : R), read (PetersenNineData.word i) j = (rows j).val.testBit (vertex i).val := by decide +kernel
private theorem extremes : ∀ x : X, read PetersenNineData.label (anchor x) = read PetersenNineLift.nine x ∧
    (read PetersenNineLift.nine x = true → below (rows (anchor x)) x) ∧
    (read PetersenNineLift.nine x = false → below x (rows (anchor x))) := by decide +kernel
private theorem base {a} (ha : a∈PetersenNineProjected.basis) : Represents rows below ((inputs 9).map read) a := by
  simp only [PetersenNineProjected.basis,List.mem_cons,PetersenNineData.sources,List.mem_ofFn] at ha
  rcases ha with rfl|rfl|⟨i,rfl⟩
  · refine ⟨fun _ => false,Av.zero,fun _ _ _ h => h,?_⟩; funext j; revert j; decide +kernel
  · refine ⟨fun _ => true,Av.one,fun _ _ _ _ => rfl,?_⟩; funext j; revert j; decide +kernel
  · refine ⟨fun x : X => x.val.testBit (vertex i).val,Av.wire ?_,?_,funext (row_word i)⟩
    · unfold inputs; rw [List.map_ofFn]; apply List.mem_ofFn.mpr; use vertex i; exact read_pack _
    · intro x y inc e; have eq := congrArg (fun z => Nat.testBit z (vertex i).val) inc
      change x.val.testBit (vertex i).val = true at e; rw [Nat.testBit_and,e,Bool.true_and] at eq; exact eq
theorem positive {k : Nat} (hard : PetersenNineLift.Hard k) : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label k := by
  intro n hn S pr out; obtain ⟨W,r,all⟩ := PetersenMonotoneSample.lift rows below (fun _ h => base h) pr
  obtain ⟨f,av,mono,eq⟩ := all _ out
  have same : f = read PetersenNineLift.nine := by
    funext x; obtain ⟨val,up,dn⟩ := extremes x
    have atRow : f (rows (anchor x)) = read PetersenNineLift.nine x := (congrFun eq (anchor x)).symm.trans val
    cases bit : read PetersenNineLift.nine x with
    | false =>
      cases z : f x with
      | false => rfl
      | true => have yes := mono x (rows (anchor x)) (dn bit) z; rw [atRow,bit] at yes; contradiction
    | true => exact mono (rows (anchor x)) x (up bit) (atRow.trans bit)
  exact hard n hn W r (same ▸ av)
#print axioms positive
end PetersenNineBoundary
