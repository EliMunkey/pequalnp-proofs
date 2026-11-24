import PetersenFastNode
open PetersenFrontier PetersenFrontierSearch PetersenPackedFrontier PetersenLayerCheck
namespace PetersenLocalChildren
variable {w : Nat}
abbrev W (n : Nat) := BitVec n
abbrev Row (n : Nat) := W n × List (W n) × Nat

def pairs (L : List (W w)) := L.flatMap fun a => L.filterMap fun b => if a.toNat<b.toNat then some (a,b) else none

def localMoves (L : List (W w)) (budget : Nat) (a b : W w) : List (Row w) :=
  (options a b).eraseDups.flatMap fun o =>
    if L.contains o then [] else
      [false,true].flatMap fun ka => [false,true].filterMap fun kb =>
        let cost := ka.toNat+kb.toNat
        if cost ≤ budget then some (o,o::kept L a b ka kb,cost) else none

def PairOK (t : W w) (d : Nat) (L : List (W w)) (pair : W w × W w) : Prop :=
  ∀ move ∈ localMoves L (d+1+1-L.toFinset.card) pair.1 pair.2, Blocked t d move.2.1

theorem pair_close {t : W w} {d L a b bank hints} (pass : PetersenFastNode.walk t bank
    (localMoves L (d+1+1-L.toFinset.card) a b) hints = true)
    (branch : ∀ v∈bank.toList, Blocked t d v) : PairOK t d L (a,b) :=
  fun _ child => PetersenFastNode.covers pass branch child

theorem finish {t : W w} {d L} (ht : t∉ L.toFinset)
    (valid : ∀ pair ∈ pairs L, PairOK t d L pair) : Blocked t (d+1) L := by
  intro m le c tail
  have total := tail_count tail
  simp only [Finset.card_singleton] at total
  generalize state : L.toFinset = S at tail
  generalize dest : ({t} : Finset _) = T at tail
  cases tail with
  | nil => exact ht ((state.trans dest.symm) ▸ Finset.mem_singleton_self _)
  | @step K a b o m c T ne fresh g tail =>
    obtain ⟨V,hit,eq⟩ := move_covers state ne (state ▸ fresh) g (by omega : credit a b K ≤ d+1+1-L.toFinset.card)
    obtain ⟨p,pm,mem⟩ := List.mem_flatMap.mp hit
    obtain ⟨q,qm,case⟩ := List.mem_flatMap.mp mem
    by_cases ord : q.toNat ≤ p.toNat
    · simp [ord] at case
    · have listed : (p,q) ∈ pairs L := by
        refine List.mem_flatMap.mpr ⟨p,pm,List.mem_filterMap.mpr ⟨q,qm,?_⟩⟩
        simp [Nat.lt_of_not_ge ord]
      have localHit : (o,V,credit a b K) ∈ localMoves L (d+1+1-L.toFinset.card) p q := by
        simpa [ord,localMoves] using case
      exact valid (p,q) listed _ localHit m (by omega) c (eq ▸ dest.symm ▸ tail)

theorem nil {α : Type*} {P : α → Prop} : ∀ x ∈ ([] : List α), P x := by simp
theorem push {α : Type*} {P : α → Prop} {x xs} (hp : P x) (rest : ∀ y∈xs, P y) :
    ∀ y∈x::xs, P y := by
  intro y mem
  rcases List.mem_cons.mp mem with rfl|h
  · exact hp
  · exact rest _ h

#print axioms finish
end PetersenLocalChildren
