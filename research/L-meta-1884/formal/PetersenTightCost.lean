import PetersenPrefixCost
import PetersenTightPrefix

open PetersenSignedBridge PetersenWordCost PetersenSignalCut PetersenShortPrefix PetersenPackedFrontier PetersenPrefixCost PetersenTightPrefix
namespace PetersenTightCost
/-- The Boolean closure certificate may use any negative-row probes and any prefix
depth. Only the gate budget and the verified truth tables enter the conclusion. -/
theorem certified {w : Nat} (hw : 0 < w) (input : List (BitVec w)) (target : BitVec w)
    (probes : Pairs w) (neg : List (Fin w)) (depth fuel : Nat)
    (normI : (input.all fun a => !(a.getLsbD 0)) = true)
    (normT : target.getLsbD 0 = false) (hotAt : Fin w) (heat : PetersenWordCost.read target hotAt = true)
    (forced : forcedSet input target probes = input.toFinset)
    (closed : tightExclude choices target neg depth fuel input = true) : NoAtMost input target fuel := by
  intro k hk W r out
  have hot : PetersenFrontier.nonconstant (PetersenWordCost.read target) := by
    constructor
    · intro h; have e := congrFun h hotAt; change PetersenWordCost.read target hotAt = false at e
      rw [heat] at e; contradiction
    · intro h; have e := congrFun h (⟨0,hw⟩ : Fin w); change target.getLsbD 0 = true at e
      rw [normT] at e; contradiction
  obtain ⟨U,us,m,hm,c,tr,_⟩ := realize hw input target
    (fun a ha => by simpa using List.all_eq_true.mp normI a ha) normT hot r out
  have tail := from_trace tr
  have eq : U = input.toFinset := by
    apply Finset.Subset.antisymm us
    intro a ha
    rw [←forced] at ha
    obtain ⟨_,f⟩ := List.mem_filter.mp (List.mem_toFinset.mp ha)
    exact must_use f (fun x hx => List.mem_toFinset.mp (us hx)) (fun i j e => determines local_gate tail i j e target (by simp))
  exact tight_sound local_gate choices (fun _ _ _ e => List.mem_eraseDups.mpr e)
    target neg depth input eq.symm (show m ≤ fuel by omega) tail closed

#print axioms certified
end PetersenTightCost
