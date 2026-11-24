import Q1020K12L0S0
open PetersenWordCost PetersenLayerCheck
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem bound (theta : Extra1020K12.Theta) : NoAtMost (inputs 8) (graphTarget 8 [(0,1),(1,2),(0,5),(1,6),(2,7),(3,5),(5,7),(7,4),(4,6),(6,3)]) 12 := by
  change NoAtMost s0_0 tgt 12
  apply root_sound (by decide)
  · intro a ha
    change a ∈ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · rfl
  · constructor
    · intro h
      have eq := congrFun h (3 : Fin 256)
      change true = false at eq
      contradiction
    · intro h
      have eq := congrFun h (0 : Fin 256)
      change false = true at eq
      contradiction
  · decide +kernel
  · exact b0_0 theta
#print axioms bound
end Orbits1020Cost12
