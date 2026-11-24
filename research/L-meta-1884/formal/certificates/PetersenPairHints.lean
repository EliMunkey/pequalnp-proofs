import PetersenFastNode
import PetersenRootOrbit
open PetersenFrontier PetersenPackedFrontier PetersenFrontierSearch PetersenLayerCheck PetersenFastNode
namespace PetersenPairHints

def casesFor {w} (L : List (BitVec w)) (a b : BitVec w) : List (BitVec w × List (BitVec w) × Nat) :=
  (options a b).eraseDups.flatMap fun o =>
    [false,true].flatMap fun ka => [false,true].map fun kb => (o,o::kept L a b ka kb,0)

theorem killed {w} {t a b : BitVec w} {k : Nat} {I : List (BitVec w)}
    {nxt : Array (List (BitVec w))} {hs : List Nat} (yes : walk t nxt (casesFor I a b) hs = true)
    (done : ∀ V∈nxt.toList, Blocked t k V) :
    PetersenRootOrbit.DeadPair t (k+1) I.toFinset a b := by
  intro K o m c eq _ _ g hm tail
  let ka := decide (a∈K)
  let kb := decide (b∈K)
  have bits (v : Bool) : v∈[false,true] := by cases v <;> simp
  have mem : (o,o::kept I a b ka kb,0) ∈ casesFor I a b := by
    apply List.mem_flatMap.mpr
    exact ⟨o,List.mem_eraseDups.mpr g,List.mem_flatMap.mpr ⟨ka,bits ka,List.mem_map.mpr ⟨kb,bits kb,rfl⟩⟩⟩
  have keep : (o::kept I a b ka kb).toFinset = insert o K := by simp only [List.toFinset_cons]; rw [kept_eq eq]
  exact covers yes done mem m (by omega) c (keep.symm ▸ tail)
end PetersenPairHints
