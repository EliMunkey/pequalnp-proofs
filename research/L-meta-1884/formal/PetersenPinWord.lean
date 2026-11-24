import PetersenWordCost
import PetersenPinDrop

open PetersenSignedBridge PetersenPinDrop
namespace PetersenWordCost

def project {p q} (ρ : Fin q → Fin p) (a : BitVec p) : BitVec q := pack (read a ∘ ρ)

def shape {p q} (lo hi : Fin q → Fin p) (a : BitVec p) : Bool :=
  project lo a == project hi a || project lo a == 0 || project lo a == ~~~0

instance {w} (W : List (BitVec w)) (a : BitVec w) : Decidable (Covered W a) := by
  unfold Covered; infer_instance

private theorem av_covered {w} {W : List (BitVec w)} {a : BitVec w} (h : Covered W a) :
    Av (W.map read) (read a) := by
  have pos {x : BitVec w} (hx : x ∈ 0 :: W) : Av (W.map read) (read x) := by
    rcases List.mem_cons.mp hx with rfl | hx
    · convert (Av.zero : Av (W.map read) (fun _ => false)) using 1
      funext i;simp [read]
    · exact Av.wire (List.mem_map.mpr ⟨x,hx,rfl⟩)
  rcases h with h | h
  · exact pos h
  · convert Av.neg (pos h) using 1
    funext i
    simp [read,i.isLt]

private theorem wordShape {p q} {lo hi : Fin q → Fin p} {a : BitVec p} :
    shape lo hi a = true ↔ Simple lo hi (read a) := by
  have same {u v : BitVec q} : read u = read v ↔ u = v := ⟨read_inj, fun h => h ▸ rfl⟩
  have zero : read (0:BitVec q) = fun _ => false := by funext i;simp [read]
  have one : read (~~~(0:BitVec q)) = fun _ => true := by funext i;simp [read,i.isLt]
  have id₁ : read (project lo a) = read a ∘ lo := read_pack _
  have id₂ : read (project hi a) = read a ∘ hi := read_pack _
  simp only [shape, Bool.or_eq_true, beq_iff_eq, Simple, ←id₁, ←id₂]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl (same.mpr h)
    · exact Or.inr ⟨false, (same.mpr h).trans zero⟩
    · exact Or.inr ⟨true, (same.mpr h).trans one⟩
  · rintro (h | ⟨c,hh⟩)
    · exact Or.inl (Or.inl (same.mp h))
    · cases c
      · exact Or.inl (Or.inr (same.mp (hh.trans zero.symm)))
      · exact Or.inr (same.mp (hh.trans one.symm))

/-- Replaying a pin certificate increases a previously established lower bound by one gate. -/
theorem lift_pin {p q K} (lo hi : Fin q → Fin p) {I : List (BitVec p)} {J : List (BitVec q)}
    {t : BitVec p} {u : BitVec q} (child : NoAtMost J u K)
    (inputCoverage : (I.all (fun a => decide (Covered J (project lo a)))) = true)
    (inputShape : (I.all (shape lo hi)) = true) (targetShape : shape lo hi t = false)
    (isTarget : project lo t = u) : NoAtMost I t (K+1) := by
  intro k hk W r h
  have coverage f (hm : f ∈ I.map read) : Av (J.map read) (f ∘ lo) := by
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
    have ok := List.all_eq_true.mp inputCoverage v hv
    exact (read_pack _ : read (project lo v) = _ ) ▸ av_covered (of_decide_eq_true ok)
  have shapes f (hm : f ∈ I.map read) : Simple lo hi f := by
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
    exact wordShape.mp (List.all_eq_true.mp inputShape v hv)
  have hc : ¬ Simple lo hi (read t) := by
    intro hs
    have yes := wordShape.mpr hs
    simp [targetShape] at yes
  obtain ⟨j,hj,V,rr,hh⟩ := shorten coverage shapes r h hc
  apply child j (by omega) V rr
  have ht : read u = read t ∘ lo := isTarget ▸ read_pack _
  exact ht ▸ hh

/-- Insert a fixed input into the list of little-endian coordinate bits. -/
def insertRow (n i : Nat) (b : Bool) (x : Fin (2^n)) : Fin (2^(n+1)) :=
  Fin.ofNat _ (x.val % 2^i + (if b then 2^i else 0) + 2^(i+1) * (x.val/2^i))

end PetersenWordCost
