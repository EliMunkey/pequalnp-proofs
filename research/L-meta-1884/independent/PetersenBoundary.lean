import Std

namespace PetersenBoundary

def edges : List (Nat × Nat) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
def target (x : Nat) : Bool := edges.any (fun (a,b) => x.testBit a && x.testBit b)
def pos : List Nat := [3, 6, 12, 13, 17, 24, 33, 66, 132, 133, 160, 264, 265, 288, 320, 321, 528, 576, 577, 640, 641]
def neg : List Nat := [50, 69, 104, 116, 138, 200, 201, 208, 276, 385, 402, 521, 548, 554, 770, 772, 773]
def below (x y : Nat) : Bool := (x % 2 == y % 2) && ((x &&& y) == x)

def cover (x : Nat) : Bool :=
  if target x then pos.any (fun y => below y x) else neg.any (fun y => below x y)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem all_covered : (List.range 1024).all cover = true := by decide

theorem size_38 : (pos ++ neg).length = 38 := by decide

theorem boundary_labels : (pos.all target && neg.all (fun y => !target y)) = true := by decide

/-- Monotonicity is needed only between rows with the same value of the marked input. -/
theorem sufficient (g : Nat → Bool)
    (mono : ∀ x y, below x y = true → g x = true → g y = true)
    (posOk : ∀ y ∈ pos, g y = true) (negOk : ∀ y ∈ neg, g y = false)
    {x : Nat} (hx : x < 1024) : g x = target x := by
  have hc : cover x = true := (List.all_eq_true.mp all_covered) x (List.mem_range.mpr hx)
  cases h : target x with
  | true =>
    simp only [cover, h, ite_true] at hc
    obtain ⟨y, hy, hle⟩ := List.any_eq_true.mp hc
    exact mono _ _ hle (posOk y hy)
  | false =>
    simp only [cover, h, Bool.false_eq_true, ite_false] at hc
    obtain ⟨y, hy, hle⟩ := List.any_eq_true.mp hc
    cases hg : g x with
    | false => rfl
    | true => simpa [negOk y hy] using mono _ _ hle hg

end PetersenBoundary
