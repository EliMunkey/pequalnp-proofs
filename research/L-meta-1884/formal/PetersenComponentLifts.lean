import PetersenCycleLifts
import PetersenCycleFive
import Certified111

open PetersenWordCost
namespace PetersenGraphCosts

theorem mask63_exact_lower : NoAtMost (inputs 6) (graphTarget 6 [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5)]) 7 :=
  (cycle_lifts PetersenCycleFive.no_six_gates).1

theorem mask127_exact_lower : NoAtMost (inputs 7)
    (graphTarget 7 [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6)]) 8 :=
  (cycle_lifts PetersenCycleFive.no_six_gates).2.1

theorem mask191_nine : NoAtMost (inputs 7)
    (graphTarget 7 [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(2,6),(5,6)]) 8 :=
  (cycle_lifts PetersenCycleFive.no_six_gates).2.2

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem mask251_exact_lower : NoAtMost (inputs 7) (graphTarget 7 [(0, 1), (2, 3), (3, 0), (0, 4), (1, 5), (4, 6)]) 7 := by
  let rows := embedding 7 6 [some 1, some 0, some 3, some 2, some 5, some 4, none]
  apply lift_pin (rows false) (rows true) M111.bound <;> decide

#print axioms mask251_exact_lower

end PetersenGraphCosts
