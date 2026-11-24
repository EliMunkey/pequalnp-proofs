import PetersenLayerCheck

open PetersenFrontier PetersenFrontierSearch PetersenPackedFrontier PetersenWordCost PetersenLayerCheck
namespace PetersenIndexedNode
variable {w : Nat}
abbrev M (w : Nat) := BitVec w × List (BitVec w) × Nat

inductive Why (w : Nat) where
  | clash (x y : Fin w)
  | member (n : Nat)

def decode (w : Nat) [NeZero w] (n : Nat) : Why w :=
  if n < w*w then .clash (Fin.ofNat w n) (Fin.ofNat w (n/w)) else .member (n-w*w)

def reasons (w stride : Nat) [NeZero w] : Nat → Nat → List (Why w)
  | 0, _ => []
  | n+1, bits => decode w (bits % (2^stride)) :: reasons w stride n (bits >>> stride)

def accepts (t : BitVec w) (bank : List (List (BitVec w))) (v : List (BitVec w)) : Why w → Bool
  | .clash x y => (PetersenWordCost.read t x != PetersenWordCost.read t y) &&
      v.all (fun a => PetersenWordCost.read a x == PetersenWordCost.read a y)
  | .member n => (bank[n]?).any (same v)

def replay (t : BitVec w) (bank : List (List (BitVec w))) : List (M w) → List (Why w) → Bool
  | [], [] => true
  | v::tail,h::hs => accepts t bank v.2.1 h && replay t bank tail hs
  | _,_ => false

private theorem checked_mem (t : BitVec w) (bank : List (List (BitVec w)))
    {ms : List (M w)} {hs : List (Why w)} (valid : replay t bank ms hs = true)
    {v : M w} (mv : v ∈ ms) : ∃ h, accepts t bank v.2.1 h = true := by
  induction ms generalizing hs with
  | nil => simp at mv
  | cons a ms ih =>
    cases hs with
    | nil => simp [replay] at valid
    | cons r hs =>
      obtain ⟨hit,rest⟩ := Bool.and_eq_true_iff.mp valid
      rcases List.mem_cons.mp mv with rfl|hm
      · exact ⟨_,hit⟩
      · exact ih rest hm

/-- Every enumerated one-gate move receives either a concrete row collision or a checked child index. -/
theorem close {t : BitVec w} {fuel : Nat} {L : List (BitVec w)} {bank : List (List (BitVec w))}
    (hints : List (Why w)) (tested : (!L.contains t &&
      replay t bank (moves L (fuel+1+1-L.toFinset.card)) hints) = true)
    (closed : ∀ b ∈ bank, Blocked t fuel b) : Blocked t (fuel+1) L := by
  intro m le c tail
  obtain ⟨miss,pass⟩ := Bool.and_eq_true_iff.mp tested
  have total := tail_count tail
  simp only [Finset.card_singleton] at total
  generalize eq : L.toFinset = S at tail
  generalize eT : ({t} : Finset (BitVec w)) = T at tail
  cases tail with
  | nil =>
    have h : t ∈ L.toFinset := (eq.trans eT.symm) ▸ Finset.mem_singleton_self _
    simpa [List.mem_toFinset.mp h] using miss
  | @step K a b o m c T ne fresh gate tail =>
    obtain ⟨V,inMoves,v⟩ := move_covers eq ne (eq ▸ fresh) gate
      (by omega : credit a b K ≤ fuel+1+1-L.toFinset.card)
    obtain ⟨why,h⟩ := checked_mem t bank pass inMoves
    have rt : Tail signedWordGate V.toFinset m c {t} := v ▸ eT.symm ▸ tail
    change accepts t bank V why = true at h
    cases why with
    | clash x y =>
      obtain ⟨diff,agree⟩ := Bool.and_eq_true_iff.mp h
      have eqs := tail_agree rt x y (fun a ha => beq_iff_eq.mp
        (List.all_eq_true.mp agree a (List.mem_toFinset.mp ha))) t (by simp)
      simp [eqs] at diff
    | member n =>
      cases e : bank[n]? with
      | none => simp [accepts,e] at h
      | some B =>
        have sameV : same V B = true := by simpa [accepts,e] using h
        exact closed B (List.mem_of_getElem? e) _ (by omega) _ (same_spec sameV ▸ rt)

#print axioms close
end PetersenIndexedNode
