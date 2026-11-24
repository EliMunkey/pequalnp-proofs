import higher.PackedPinReuse
import PetersenPermuteWord

open PetersenPackedPin PetersenPermuteWord
namespace PetersenFastGather
variable {w u : Nat}

def gather (p : List (Nat × BitVec w)) (a : BitVec w) : BitVec u :=
  (pieces p a).setWidth u

theorem correct (uw : u ≤ w) (r : Fin u → Fin w) (p : List (Nat × BitVec w))
    (check : ∀ i : Fin u, picked p ⟨i.val,lt_of_lt_of_le i.isLt uw⟩ = [(r i).val])
    (a : BitVec w) : PetersenPackedPin.project r a = gather p a := by
  apply PetersenWordCost.read_inj
  rw [PetersenPackedPin.project,PetersenWordCost.read_pack]
  funext i
  have v := pieces_read p a ⟨i.val,lt_of_lt_of_le i.isLt uw⟩
  rw [check i] at v
  simpa [gather,PetersenWordCost.read,i.isLt] using v.symm

def estimate (f : BitVec w → BitVec u) (I : List (BitVec u)) (K : Nat) (pr : List Instr)
    (L : List (BitVec w)) (fuel : Nat) : Bool :=
  let values := L.map f
  decide L.Nodup && values.all (PetersenForwardSearch.cb (replay I pr)) &&
    decide (pr.length+fuel < K+1+(values.filter fun a => a == 0 || a == ~~~0).length)

theorem estimate_sound (r : Fin u → Fin w) (f : BitVec w → BitVec u)
    (eq : ∀ a, PetersenPackedPin.project r a = f a) (I : List (BitVec u)) (K : Nat)
    (pr : List Instr) (L : List (BitVec w)) (fuel : Nat)
    (ok : estimate f I K pr L fuel = true) : rejects r I K pr L fuel = true := by
  obtain ⟨both,lim⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨nd,cov⟩ := Bool.and_eq_true_iff.mp both
  apply PetersenReusableProjection.rejects_of_projection _ _ _ _ _ _ (L.map f)
  · rw [funext eq]
  · exact of_decide_eq_true nd
  · exact cov
  · exact of_decide_eq_true lim

#print axioms correct
#print axioms estimate_sound
end PetersenFastGather
