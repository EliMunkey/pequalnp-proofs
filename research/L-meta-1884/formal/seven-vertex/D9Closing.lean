import D9L0S0
open PetersenWordCost PetersenLayerCheck
namespace Deleted191Cost9
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem bound : NoAtMost (inputs 7) (graphTarget 7 [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(2,6),(5,6)]) 9 := by
  change NoAtMost s0_0 tgt 9
  apply root_sound (by decide)
  · intro a ha
    change a ∈ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · rfl
  · constructor
    · intro h
      have eq := congrFun h (3 : Fin 128)
      change true = false at eq
      contradiction
    · intro h
      have eq := congrFun h (0 : Fin 128)
      change false = true at eq
      contradiction
  · decide +kernel
  · exact b0_0
#print axioms bound
end Deleted191Cost9
