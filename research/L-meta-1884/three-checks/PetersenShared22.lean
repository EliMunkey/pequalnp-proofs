import PetersenScalarModels
import PetersenDominantPin
open PetersenWordCost PetersenPackedPin PetersenPhysicalWords PetersenPhysicalProjection
open PetersenNineData PetersenCubicScalar
namespace PetersenShared22
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sample : Fin 22 → Fin 24 := ![0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,18,19,20,21,22,23]
def inputs22 := PetersenNineProjected.basis.map (project sample)
def target22 := project sample label
def Hard (k : Nat) := NoPhysical inputs22 target22 k

theorem mapRun (r : Fin u → Fin w) {I : List (BitVec w)} {k W} (run : Positive I k W) :
    Positive (I.map (project r)) k (W.map (project r)) := by
  induction run with
  | start => exact Positive.start
  | @add n X a b o _ ha hb ih =>
    simp only [List.map_cons,PetersenDominantPin.projectGate]
    exact Positive.add o ih (List.mem_map.mpr ⟨_,ha,rfl⟩) (List.mem_map.mpr ⟨_,hb,rfl⟩)

private theorem liftRun (r : Fin u → Fin w) {B : List (BitVec u)} {k W}
    (run : Positive B k W) (I : List (BitVec w)) (h : B=I.map (project r)) :
    ∃ V, Positive I k V ∧ W=V.map (project r) := by
  induction run with
  | start => exact ⟨I, Positive.start, h⟩
  | @add n X a b o _ ha hb ih =>
    obtain ⟨V,earlier,eq⟩ := ih
    rw [eq] at ha hb
    obtain ⟨a',mem,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b',mem',rfl⟩ := List.mem_map.mp hb
    exact ⟨_,Positive.add o earlier mem mem',by rw [List.map_cons,PetersenDominantPin.projectGate,eq]⟩

private theorem restrict_scalar (p q : Bool) : project sample (scalar p q)=target22 := by
  revert p q; decide +kernel

theorem excludes (h : Hard k) (p q : Bool) : NoPhysical PetersenNineProjected.basis (scalar p q) k := by
  intro n le W run mem
  apply h n le _ (mapRun sample run)
  rw [←restrict_scalar p q]
  exact List.mem_map.mpr ⟨_,mem,rfl⟩

private theorem bits (p q : Bool) (j : Fin 24) : read (scalar p q) j =
    (if j=6 then p else if j=17 then q else read label j) := by
  revert p q j; decide +kernel

private theorem recover (v : BitVec 24) (agree : project sample v=target22) :
    v=scalar (read v 6) (read v 17) := by
  apply read_inj
  funext j
  rw [bits]
  split
  · rename_i e;rw [e]
  split
  · rename_i e;rw [e]
  rename_i q
  have coverage : ∀ j : Fin 24, j=6 ∨ j=17 ∨ ∃ i, sample i=j := by decide +kernel
  rcases coverage j with e|e|⟨i,rfl⟩
  · contradiction
  · contradiction
  · have e := congrArg (fun w : BitVec 22 => read w i) agree
    simpa [target22,project,read_pack,Function.comp_def] using e

theorem equivalent (k : Nat) : Hard k ↔ ∀ p q, NoPhysical PetersenNineProjected.basis (scalar p q) k := by
  constructor
  · exact excludes
  · intro h n le W run mem
    obtain ⟨V,old,eq⟩ := liftRun sample run PetersenNineProjected.basis rfl
    rw [eq] at mem
    obtain ⟨v,found,agree⟩ := List.mem_map.mp mem
    exact h (read v 6) (read v 17) n le V old (recover v agree ▸ found)

#print axioms equivalent
end PetersenShared22
