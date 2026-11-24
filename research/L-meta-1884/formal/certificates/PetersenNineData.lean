import PetersenFrontierSymmetry
import PetersenMonotoneFrontier
open PetersenWordCost PetersenFrontierSymmetry
namespace PetersenNineData
abbrev V := Fin 9
abbrev R := Fin 24
abbrev B := BitVec 24
set_option maxRecDepth 25000
set_option maxHeartbeats 0
def word : V → B := ![0x428229,0x8021c3,0xa1a06,0x4a454,0x890898,0x104ce0,0x218f00,0xc1f000,0xfe0000]
def label : B := 0x34513f
def rowCode : R → Nat := ![3,6,12,17,24,33,42,50,66,69,104,116,132,138,160,201,208,261,264,276,288,320,385,402]
def row (j : R) : V → Bool := fun i => (rowCode j).testBit i.val
def target (x : V → Bool) : Bool := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
def sources : List B := List.ofFn word
def raw : List ((V → Bool) → Bool) := (fun _ => false) :: (fun _ => true) :: (List.ofFn (fun (i : V) (x : V→Bool) => x i))
theorem target_ok : pack (target ∘ row)=label := by decide
theorem primary_ok (i : V) : pack ((fun x : V → Bool => x i) ∘ row)=word i := by revert i; decide
structure Aut where
  row : R ≃ R
  vertex : V ≃ V
  primary : ∀ i j, read (word i) (row j) = read (word (vertex i)) j
  target : ∀ j, read label (row j) = read label j
private def g0 : Aut := by
  let f : V → V := ![0,1,2,3,4,5,6,7,8]
  let g : V → V := ![0,1,2,3,4,5,6,7,8]
  let a : R → R := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23]
  let b : R → R := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide⟩
private def g1 : Aut := by
  let f : V → V := ![0,5,8,3,4,1,7,6,2]
  let g : V → V := ![0,5,8,3,4,1,7,6,2]
  let a : R → R := ![5,20,18,3,4,0,6,7,14,22,13,23,21,10,8,15,16,17,2,19,1,12,9,11]
  let b : R → R := ![5,20,18,3,4,0,6,7,14,22,13,23,21,10,8,15,16,17,2,19,1,12,9,11]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide⟩
private def g2 : Aut := by
  let f : V → V := ![1,0,5,8,6,2,4,7,3]
  let g : V → V := ![1,0,5,8,6,2,4,7,3]
  let a : R → R := ![0,5,20,8,21,1,17,9,3,7,19,11,14,22,12,23,16,6,18,10,2,4,13,15]
  let b : R → R := ![0,5,20,8,21,1,17,9,3,7,19,11,14,22,12,23,16,6,18,10,2,4,13,15]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide⟩
private def g3 : Aut := by
  let f : V → V := ![1,2,3,8,6,0,7,4,5]
  let g : V → V := ![5,0,1,2,7,8,4,6,3]
  let a : R → R := ![5,0,1,14,12,20,17,22,3,7,19,23,8,9,21,11,16,6,2,13,18,4,10,15]
  let b : R → R := ![1,2,18,8,21,0,17,9,12,13,22,15,4,19,3,23,16,6,20,10,5,14,7,11]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide⟩
private def g4 : Aut := by
  let f : V → V := ![2,1,0,5,7,3,6,4,8]
  let g : V → V := ![2,1,0,5,7,3,6,4,8]
  let a : R → R := ![1,0,5,12,14,2,6,13,8,9,10,15,3,7,4,11,16,17,20,22,18,21,19,23]
  let b : R → R := ![1,0,5,12,14,2,6,13,8,9,10,15,3,7,4,11,16,17,20,22,18,21,19,23]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide⟩
private def g5 : Aut := by
  let f : V → V := ![2,3,8,5,7,1,4,6,0]
  let g : V → V := ![8,5,0,1,6,3,7,4,2]
  let a : R → R := ![20,5,0,21,8,18,6,10,14,22,13,15,3,7,4,23,16,17,1,9,2,12,19,11]
  let b : R → R := ![2,18,20,12,14,1,6,13,4,19,7,23,21,10,8,11,16,17,5,22,0,3,9,15]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide⟩
private def g6 : Aut := by
  let f : V → V := ![3,2,1,0,4,8,7,6,5]
  let g : V → V := ![3,2,1,0,4,8,7,6,5]
  let a : R → R := ![2,1,0,4,3,18,17,19,12,13,22,23,8,9,21,15,16,6,5,7,20,14,10,11]
  let b : R → R := ![2,1,0,4,3,18,17,19,12,13,22,23,8,9,21,15,16,6,5,7,20,14,10,11]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide⟩
private def g7 : Aut := by
  let f : V → V := ![3,8,5,0,4,2,6,7,1]
  let g : V → V := ![3,8,5,0,4,2,6,7,1]
  let a : R → R := ![18,20,5,4,3,2,17,19,21,10,9,11,14,22,12,15,16,6,0,7,1,8,13,23]
  let b : R → R := ![18,20,5,4,3,2,17,19,21,10,9,11,14,22,12,15,16,6,0,7,1,8,13,23]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide⟩
private def g8 : Aut := by
  let f : V → V := ![5,0,1,2,7,8,4,6,3]
  let g : V → V := ![1,2,3,8,6,0,7,4,5]
  let a : R → R := ![1,2,18,8,21,0,17,9,12,13,22,15,4,19,3,23,16,6,20,10,5,14,7,11]
  let b : R → R := ![5,0,1,14,12,20,17,22,3,7,19,23,8,9,21,11,16,6,2,13,18,4,10,15]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide⟩
private def g9 : Aut := by
  let f : V → V := ![5,8,3,2,7,0,6,4,1]
  let g : V → V := ![5,8,3,2,7,0,6,4,1]
  let a : R → R := ![20,18,2,14,12,5,17,22,21,10,9,15,4,19,3,11,16,6,1,13,0,8,7,23]
  let b : R → R := ![20,18,2,14,12,5,17,22,21,10,9,15,4,19,3,11,16,6,1,13,0,8,7,23]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide⟩
private def g10 : Aut := by
  let f : V → V := ![8,3,2,1,6,5,4,7,0]
  let g : V → V := ![8,3,2,1,6,5,4,7,0]
  let a : R → R := ![18,2,1,21,8,20,6,10,4,19,7,11,12,13,14,23,16,17,0,9,5,3,22,15]
  let b : R → R := ![18,2,1,21,8,20,6,10,4,19,7,11,12,13,14,23,16,17,0,9,5,3,22,15]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide⟩
private def g11 : Aut := by
  let f : V → V := ![8,5,0,1,6,3,7,4,2]
  let g : V → V := ![2,3,8,5,7,1,4,6,0]
  let a : R → R := ![2,18,20,12,14,1,6,13,4,19,7,23,21,10,8,11,16,17,5,22,0,3,9,15]
  let b : R → R := ![20,5,0,21,8,18,6,10,14,22,13,15,3,7,4,23,16,17,1,9,2,12,19,11]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide⟩
def group : Fin 12 → Aut := ![g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11]
def choice : V → V → Fin 12 := ![![0,0,0,0,0,1,0,1,1],![0,2,4,6,2,2,2,8,2],![0,4,4,6,11,3,4,4,10],![0,6,6,6,6,7,7,6,7],![0,2,11,6,0,3,0,1,10],![1,2,3,7,3,3,9,3,5],![0,2,4,7,0,9,2,4,5],![1,8,4,6,1,3,4,3,5],![1,2,10,7,10,5,5,5,5]]
def first : V → V → V := ![![0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0],![0,0,0,0,4,0,4,4,0],![0,0,0,0,0,0,0,0,0],![0,0,0,0,4,0,4,4,0],![0,0,0,0,4,0,4,4,0],![0,0,0,0,0,0,0,0,0]]
def second : V → V → V := ![![0,1,2,3,4,1,6,6,2],![1,0,1,2,6,2,4,6,3],![2,1,0,1,6,3,6,4,2],![3,2,1,0,4,2,6,6,1],![4,6,6,4,4,6,6,6,6],![1,2,3,2,6,0,6,4,1],![6,4,6,6,6,6,4,6,4],![6,6,4,6,6,4,6,4,6],![2,3,2,1,6,1,4,6,0]]
def reps : List (V×V) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (4, 6)]
def pick (i j : V) : Aut := group (choice i j)
theorem witness (i j : V) (ne : i ≠ j) :
    (first i j,second i j)∈reps ∧
     (((pick i j).vertex i=first i j ∧ (pick i j).vertex j=second i j) ∨
      ((pick i j).vertex j=first i j ∧ (pick i j).vertex i=second i j)) := by
  revert i j; decide +kernel

theorem primary_act (a : Aut) (i : V) : act a.row (word i) = word (a.vertex i) :=
  (act_eq_iff ..).mpr (a.primary i)
theorem target_act (a : Aut) : act a.row label = label := (act_eq_iff ..).mpr a.target
#print axioms primary_ok
end PetersenNineData
