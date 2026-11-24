import PetersenSmallPins

open PetersenWordCost
namespace PetersenGraphCosts

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
/-- Three induced-graph bounds discharged as soon as the five-cycle cost is available. -/
theorem cycle_lifts (c5 : NoAtMost (inputs 5)
      (graphTarget 5 [(0,1),(1,2),(2,3),(3,4),(4,0)]) 6) :
    NoAtMost (inputs 6) (graphTarget 6 [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5)]) 7 ∧
    NoAtMost (inputs 7) (graphTarget 7 [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6)]) 8 ∧
    NoAtMost (inputs 7) (graphTarget 7 [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(2,6),(5,6)]) 8 := by
  have stage : NoAtMost (inputs 6) (graphTarget 6 [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5)]) 7 := by
    let rows := embedding 6 5 [some 0,some 1,some 2,some 3,some 4,none]
    apply lift_pin (rows false) (rows true) c5 <;> decide
  refine ⟨stage,?_,?_⟩
  · let rows := embedding 7 6 [some 0,some 1,some 2,some 3,some 4,some 5,none]
    apply lift_pin (rows false) (rows true) stage <;> decide
  · let rows := embedding 7 6 [some 0,some 1,some 2,some 3,some 4,some 5,none]
    apply lift_pin (rows false) (rows true) stage <;> decide

end PetersenGraphCosts
