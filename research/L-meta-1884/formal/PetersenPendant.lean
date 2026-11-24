import PetersenWordCost
import PetersenPinDrop

open PetersenSignedBridge PetersenWordCost PetersenPinDrop
namespace PetersenPendant

def cycle5 : List (Nat × Nat) := [(0,1),(1,2),(2,3),(3,4),(4,0)]
def pendant : List (Nat × Nat) := cycle5 ++ [(0,5)]
def lo (a : Fin 32) : Fin 64 := ⟨a.val,by omega⟩
def hi (a : Fin 32) : Fin 64 := ⟨a.val+32,by omega⟩
def col (n : Nat) (j : Fin n) : Func (Fin (2^n)) := fun r => r.val.testBit j.val

theorem col_mem {n : Nat} {f : Func (Fin (2^n))} :
    f ∈ (inputs n).map read ↔ ∃ j : Fin n, f=col n j := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    exact ⟨j,read_pack _⟩
  · rintro ⟨j,rfl⟩
    exact List.mem_map.mpr ⟨pack (col n j),List.mem_ofFn.mpr ⟨j,rfl⟩,read_pack _⟩

theorem lat {j : Fin 6} (h : j.val < 5) : col 6 j ∘ lo = col 5 ⟨j.val,h⟩ := rfl

theorem small (j : Fin 6) (h : j.val < 5) : col 6 j ∘ lo = col 6 j ∘ hi := by
  funext x
  revert j x
  decide

theorem fixed (j : Fin 6) (h : ¬ j.val < 5) : col 6 j ∘ lo = fun _ => false := by
  funext x
  revert j x
  decide

theorem restricted :
    PetersenWordCost.read (graphTarget 6 pendant) ∘ lo = PetersenWordCost.read (graphTarget 5 cycle5) := by
  unfold graphTarget
  rw [read_pack,read_pack]
  funext x; revert x; decide

theorem nonsimple : ¬ Simple lo hi (PetersenWordCost.read (graphTarget 6 pendant)) := by
  unfold graphTarget
  rw [read_pack]
  rintro (e|⟨b,e⟩)
  · have diff := congrFun e (1 : Fin 32)
    change false = true at diff
    contradiction
  · cases b
    · have diff := congrFun e (3 : Fin 32)
      change true = false at diff
      contradiction
    · have diff := congrFun e (0 : Fin 32)
      change false = true at diff
      contradiction

/-- Deleting vertex 5 from graph mask 63 leaves C5. The specialized run
loses at least one gate even in U2 with free complemented wires. -/
theorem mask63_of_cycle5 (h5 : NoAtMost (inputs 5) (graphTarget 5 cycle5) 6) :
    NoAtMost (inputs 6) (graphTarget 6 pendant) 7 := by
  intro k hk W run out
  have avail : ∀ f ∈ (inputs 6).map read, Av ((inputs 5).map read) (f ∘ lo) := by
    intro f hf
    obtain ⟨j,rfl⟩ := col_mem.mp hf
    by_cases h : j.val < 5
    · rw [lat h]; exact Av.wire (col_mem.mpr ⟨_,rfl⟩)
    · rw [fixed j h]; exact Av.zero
  have shapes : ∀ f ∈ (inputs 6).map read, Simple lo hi f := by
    intro f hf
    obtain ⟨j,rfl⟩ := col_mem.mp hf
    by_cases h : j.val < 5
    · exact Or.inl (small j h)
    · exact Or.inr ⟨false,fixed j h⟩
  obtain ⟨j,hj,S,r,v⟩ := shorten avail shapes run out nonsimple
  rw [restricted] at v
  exact h5 j (by omega) S r v

#print axioms mask63_of_cycle5
end PetersenPendant
