import PetersenPinWord
import PetersenPathFour

open PetersenWordCost
namespace PetersenGraphCosts

/-- Each present entry specifies a surviving, possibly reordered primary. An absent entry is pinned. -/
def embedding (n m : Nat) (permutation : List (Option Nat)) (fixed : Bool) (x : Fin (2^m)) : Fin (2^n) :=
  Fin.ofNat _ (permutation.foldr (fun o acc => 2*acc + (if o.elim fixed (fun j => x.val.testBit j) then 1 else 0)) 0)

abbrev mask15_lower : NoAtMost (inputs 4) (graphTarget 4 [(0,1),(1,2),(2,3)]) 3 :=
  PetersenPathFour.no_three_gates

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem mask47_lower : NoAtMost (inputs 5) (graphTarget 5 [(0, 1), (1, 2), (2, 3), (0, 4)]) 4 := by
  let rows := embedding 5 4 [some 0, some 1, some 2, some 3, none]
  apply lift_pin (rows false) (rows true) mask15_lower <;> decide

#print axioms mask47_lower

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem mask55_lower : NoAtMost (inputs 5) (graphTarget 5 [(0, 1), (1, 2), (3, 0), (0, 4)]) 4 := by
  let rows := embedding 5 4 [some 2, some 1, some 0, some 3, none]
  apply lift_pin (rows false) (rows true) mask15_lower <;> decide

#print axioms mask55_lower

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem mask111_lower : NoAtMost (inputs 6) (graphTarget 6 [(0, 1), (1, 2), (2, 3), (0, 4), (1, 5)]) 5 := by
  let rows := embedding 6 5 [some 0, some 1, some 2, some 3, some 4, none]
  apply lift_pin (rows false) (rows true) mask47_lower <;> decide

#print axioms mask111_lower

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem mask119_lower : NoAtMost (inputs 6) (graphTarget 6 [(0, 1), (1, 2), (3, 0), (0, 4), (1, 5)]) 5 := by
  let rows := embedding 6 5 [some 0, some 1, some 2, some 3, some 4, none]
  apply lift_pin (rows false) (rows true) mask55_lower <;> decide

#print axioms mask119_lower

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem mask63_lower : NoAtMost (inputs 6) (graphTarget 6 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5)]) 5 := by
  let rows := embedding 6 5 [some 0, some 1, some 2, some 3, none, some 4]
  apply lift_pin (rows false) (rows true) mask47_lower <;> decide

#print axioms mask63_lower

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem mask189_lower : NoAtMost (inputs 6) (graphTarget 6 [(1, 2), (2, 3), (3, 0), (0, 4), (1, 5), (4, 5)]) 5 := by
  let rows := embedding 6 5 [some 0, some 3, some 2, some 1, some 4, none]
  apply lift_pin (rows false) (rows true) mask47_lower <;> decide

#print axioms mask189_lower

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem mask127_lower : NoAtMost (inputs 7) (graphTarget 7 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6)]) 6 := by
  let rows := embedding 7 6 [some 0, some 1, some 2, some 3, none, some 4, some 5]
  apply lift_pin (rows false) (rows true) mask111_lower <;> decide

#print axioms mask127_lower

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem mask191_lower : NoAtMost (inputs 7) (graphTarget 7 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (2, 6), (5, 6)]) 6 := by
  let rows := embedding 7 6 [none, some 5, some 1, some 0, some 4, some 3, some 2]
  apply lift_pin (rows false) (rows true) mask111_lower <;> decide

#print axioms mask191_lower

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem mask251_lower : NoAtMost (inputs 7) (graphTarget 7 [(0, 1), (2, 3), (3, 0), (0, 4), (1, 5), (4, 6)]) 6 := by
  let rows := embedding 7 6 [some 1, some 0, some 3, some 2, some 5, some 4, none]
  apply lift_pin (rows false) (rows true) mask111_lower <;> decide

#print axioms mask251_lower

end PetersenGraphCosts
