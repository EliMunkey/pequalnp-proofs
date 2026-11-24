import PetersenBitBank
open PetersenLayerCheck PetersenBank PetersenBitBank
namespace PetersenRuleBank
variable {w n : Nat}

structure Rule where
  cover : Nat
  fixed : Nat
  budget : Nat
  cost : Nat

def Correct (word : Fin n → BitVec w) (t : BitVec w) (r : Rule) : Prop :=
  ∀ {fuel L}, fits r.cover r.fixed fuel r.budget r.cost L = true → Blocked t fuel (L.map word)

def test (tab : Nat → Rule) (which : Nat → Nat) (ids : Nat → List (Fin n))
    (fuel i : Nat) : Bool :=
  let r := tab (which i)
  fits r.cover r.fixed fuel r.budget r.cost (ids i)

theorem children {tab : Nat → Rule} {which : Nat → Nat} {ids : Nat → List (Fin n)} {fuel : Nat}
    {word : Fin n → BitVec w} {t : BitVec w} (ok : ∀ i, Correct word t (tab i))
    {kids : Array Nat} {more : List Nat}
    (testOK : kids.toList.all (fun i => more.contains i || test tab which ids fuel i) = true)
    (done : ∀ i∈more, Blocked t fuel ((ids i).map word)) :
    ∀ V∈(kids.map fun i => (ids i).map word).toList, Blocked t fuel V := by
  intro V mem
  simp only [Array.toList_map,List.mem_map] at mem
  obtain ⟨i,hi,rfl⟩ := mem
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp testOK i hi) with h|h
  · exact done i (List.contains_iff_mem.mp h)
  · exact ok (which i) h

def get (A : Array Rule) (i : Nat) (fallback : Rule) : Rule := (A[i]?).getD fallback

theorem entries {word : Fin n → BitVec w} {t : BitVec w} {A : Array Rule} {fallback : Rule}
    (fallback_ok : Correct word t fallback) (each : ∀ r∈A.toList, Correct word t r) :
    ∀ i, Correct word t (get A i fallback) := by
  intro i
  unfold get
  cases eq : A[i]? with
  | none => exact fallback_ok
  | some v => exact each v (by simpa using Array.mem_of_getElem? eq)

end PetersenRuleBank
