import PetersenForwardSearch

open PetersenWordCost PetersenSignalCut PetersenForwardSearch
namespace PetersenGraphCosts

set_option maxRecDepth 16000 in
theorem mask45_lower : NoAtMost (inputs 4) (graphTarget 4 [(1, 2), (0, 3)]) 2 := by
  apply lower_of_reject
  exact search_sound ([(8, 9), (4, 6), (2, 6), (1, 9)] : Pairs 16) [] 2 (inputs 4) (by decide)
#print axioms mask45_lower

set_option maxRecDepth 16000 in
theorem mask51_lower : NoAtMost (inputs 4) (graphTarget 4 [(0, 1), (2, 0), (0, 3)]) 2 := by
  apply lower_of_reject
  exact search_sound ([(2, 3), (1, 3), (1, 5), (1, 9)] : Pairs 16) [] 2 (inputs 4) (by decide)
#print axioms mask51_lower

set_option maxRecDepth 16000 in
theorem mask250_lower : NoAtMost (inputs 6) (graphTarget 6 [(1, 2), (0, 4), (3, 5)]) 4 := by
  apply lower_of_reject
  exact search_sound ([(16, 17), (4, 6), (2, 6), (32, 40), (1, 17), (8, 40)] : Pairs 64) [] 4 (inputs 6) (by decide)
#print axioms mask250_lower
end PetersenGraphCosts
