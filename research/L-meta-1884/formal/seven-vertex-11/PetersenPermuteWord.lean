import PetersenSymmetry

open PetersenWordCost PetersenSymmetry
namespace PetersenPermuteWord
variable {w : Nat}

def source (w r i : Nat) : Nat :=
  if i < w-(r%w) then r%w+i else i-(w-(r%w))

def pieces (program : List (Nat × BitVec w)) (a : BitVec w) : BitVec w :=
  program.foldr (fun (n,mask) acc => (mask &&& a.rotateRight n) ||| acc) 0

def picked (program : List (Nat × BitVec w)) (i : Fin w) : List Nat :=
  program.filterMap fun (n,mask) => if mask.getLsbD i.val then some (source w n i.val) else none

theorem pieces_read (program : List (Nat × BitVec w)) (a : BitVec w) (i : Fin w) :
    PetersenWordCost.read (pieces program a) i = (picked program i).any (a.getLsbD ·) := by
  induction program with
  | nil => simp [pieces,picked,PetersenWordCost.read]
  | cons x xs ih =>
    obtain ⟨n,mask⟩ := x
    change ((mask &&& a.rotateRight n) ||| pieces xs a).getLsbD i.val = _
    simp only [BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_rotateRight,i.isLt,decide_true,Bool.true_and]
    change (mask.getLsbD i.val && _ || PetersenWordCost.read (pieces xs a) i) = _
    rw [ih]
    have pc : picked ((n,mask)::xs) i = if mask.getLsbD i.val then source w n i.val :: picked xs i else picked xs i := by
      unfold picked; rw [List.filterMap_cons]; cases h : mask.getLsbD i.val <;> simp only [h,Bool.false_eq_true,ite_false,ite_true] <;> rfl
    rw [pc]
    cases hm : mask.getLsbD i.val <;> by_cases low : i.val < w-(n%w) <;> simp only [hm,Bool.false_eq_true,ite_false,ite_true,Bool.false_and,Bool.true_and,Bool.false_or,List.any_cons,source,low]

def action (hw : 0<w) (r : Fin w → Fin w) (inv : ∀ i, r (r i) = i)
    (zero : r ⟨0,hw⟩ = ⟨0,hw⟩) (p : List (Nat × BitVec w))
    (verify : ∀ i : Fin w, picked p i = [(r i).val]) : Action w :=
  ofRows hw r (fun i => ⟨r i,inv _⟩) zero (pieces p) (by
    intro a i; rw [pieces_read,verify]; simp [PetersenWordCost.read])

#print axioms action
end PetersenPermuteWord
