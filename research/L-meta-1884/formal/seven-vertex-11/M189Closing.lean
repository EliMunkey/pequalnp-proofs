import M189L0S0
open PetersenWordCost PetersenFrontier PetersenLayerCheck
namespace M189Certificate
set_option maxRecDepth 30000
def edges : List (Nat × Nat) := [(1,2),(2,3),(3,0),(0,4),(1,5),(4,5)]

theorem graph_bits : graphTarget 6 edges = t := by
  apply read_inj
  change read (pack _) = read t
  rw [read_pack]; funext i; revert i; decide

theorem input_bits : inputs 6 = s0_0 := by
  let data : Fin 6 → BitVec 64 := ![0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
  have h (i : Fin 6) : pack (fun j : Fin 64 => j.val.testBit i.val) = data i := by
    apply read_inj; rw [read_pack]; funext j; revert i j; decide
  exact (congrArg (fun (f : Fin 6 → BitVec 64) => List.ofFn f) (funext h)).trans (by rfl)

theorem lower : NoAtMost (inputs 6) (graphTarget 6 edges) 7 := by
  rw [input_bits,graph_bits]
  apply root_sound (by decide)
  · intro a ha
    change a ∈ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · rfl
  · constructor
    · intro h
      have eq := congrFun h (6 : Fin 64)
      change true = false at eq
      exact Bool.noConfusion eq
    · intro h
      have eq := congrFun h (0 : Fin 64)
      change false = true at eq
      exact Bool.noConfusion eq
  · rfl
  · exact b0_0
#print axioms lower
end M189Certificate
