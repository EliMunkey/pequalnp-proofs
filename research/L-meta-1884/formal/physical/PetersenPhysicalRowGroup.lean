import PetersenFrontierSymmetry
import PetersenPhysicalDemand
open PetersenWordCost PetersenFrontierSymmetry PetersenPhysicalWords
namespace PetersenPhysicalRowGroup
abbrev V := Fin 10
abbrev R := Fin 38
set_option maxHeartbeats 2500000
set_option maxRecDepth 45000


def word : V → BitVec 38 := ![0x250b122259,0x844004183,0x3020203a0e,0x481b442c,0x142408b0,0x60408cc0,0x181870f00,0x60607f000,0x3807f80000,0x3ff8000000]

def label : BitVec 38 := 0x791d8b17f

theorem initial_eq : input = List.ofFn word := by decide
theorem target_eq : target = label := by decide
theorem pivot_eq : pivot = word 0 := by decide
structure Aut where
  row : R ≃ R
  vertex : V ≃ V
  fixes : vertex 0 = 0
  primary : ∀ i j, read (word i) (row j) = read (word (vertex i)) j
  target : ∀ j, read label (row j) = read label j


private def sym0 : Aut := by
  let f : V → V := ![0,1,2,3,4,5,6,7,8,9]
  let g : V → V := ![0,1,2,3,4,5,6,7,8,9]
  let a : R → R := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  let b : R → R := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide,by decide⟩

private def sym1 : Aut := by
  let f : V → V := ![0,1,2,7,5,4,6,3,9,8]
  let g : V → V := ![0,1,2,7,5,4,6,3,9,8]
  let a : R → R := ![0,1,12,13,6,15,4,7,8,9,18,11,2,3,14,5,16,17,10,33,34,29,28,31,32,27,30,25,22,21,26,23,24,19,20,35,36,37]
  let b : R → R := ![0,1,12,13,6,15,4,7,8,9,18,11,2,3,14,5,16,17,10,33,34,29,28,31,32,27,30,25,22,21,26,23,24,19,20,35,36,37]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide,by decide⟩

private def sym2 : Aut := by
  let f : V → V := ![0,1,6,8,5,4,2,9,3,7]
  let g : V → V := ![0,1,6,8,5,4,2,9,3,7]
  let a : R → R := ![0,8,23,24,6,22,4,7,1,9,21,11,31,32,35,28,36,37,29,19,20,10,5,2,3,27,30,25,15,18,26,12,13,33,34,14,16,17]
  let b : R → R := ![0,8,23,24,6,22,4,7,1,9,21,11,31,32,35,28,36,37,29,19,20,10,5,2,3,27,30,25,15,18,26,12,13,33,34,14,16,17]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide,by decide⟩

private def sym3 : Aut := by
  let f : V → V := ![0,1,6,9,4,5,2,8,7,3]
  let g : V → V := ![0,1,6,9,4,5,2,8,7,3]
  let a : R → R := ![0,8,31,32,4,28,6,7,1,9,29,11,23,24,35,22,36,37,21,33,34,18,15,12,13,25,26,27,5,10,30,2,3,19,20,14,16,17]
  let b : R → R := ![0,8,31,32,4,28,6,7,1,9,29,11,23,24,35,22,36,37,21,33,34,18,15,12,13,25,26,27,5,10,30,2,3,19,20,14,16,17]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide,by decide⟩

private def sym4 : Aut := by
  let f : V → V := ![0,4,3,2,1,5,9,8,7,6]
  let g : V → V := ![0,4,3,2,1,5,9,8,7,6]
  let a : R → R := ![4,5,2,3,0,1,6,7,28,27,29,30,19,20,21,22,36,37,35,12,13,14,15,33,34,25,26,9,8,10,11,31,32,23,24,18,16,17]
  let b : R → R := ![4,5,2,3,0,1,6,7,28,27,29,30,19,20,21,22,36,37,35,12,13,14,15,33,34,25,26,9,8,10,11,31,32,23,24,18,16,17]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide,by decide⟩

private def sym5 : Aut := by
  let f : V → V := ![0,4,3,8,5,1,9,2,6,7]
  let g : V → V := ![0,5,7,2,1,4,8,9,3,6]
  let a : R → R := ![6,15,12,13,0,1,4,7,22,25,21,26,33,34,29,28,36,37,35,2,3,14,5,19,20,27,30,9,8,18,11,23,24,31,32,10,16,17]
  let b : R → R := ![4,5,19,20,6,22,0,7,28,27,35,30,2,3,21,1,36,37,29,23,24,10,8,31,32,9,11,25,15,14,26,33,34,12,13,18,16,17]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide,by decide⟩

private def sym6 : Aut := by
  let f : V → V := ![0,4,9,6,1,5,3,7,8,2]
  let g : V → V := ![0,4,9,6,1,5,3,7,8,2]
  let a : R → R := ![4,28,31,32,0,8,6,7,5,27,10,30,33,34,18,15,16,17,14,23,24,35,22,19,20,25,26,9,1,29,11,2,3,12,13,21,36,37]
  let b : R → R := ![4,28,31,32,0,8,6,7,5,27,10,30,33,34,18,15,16,17,14,23,24,35,22,19,20,25,26,9,1,29,11,2,3,12,13,21,36,37]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide,by decide⟩

private def sym7 : Aut := by
  let f : V → V := ![0,4,9,7,5,1,3,6,2,8]
  let g : V → V := ![0,5,8,6,1,4,7,3,9,2]
  let a : R → R := ![6,22,23,24,0,8,4,7,15,25,18,26,19,20,10,5,16,17,14,31,32,35,28,33,34,27,30,9,1,21,11,12,13,2,3,29,36,37]
  let b : R → R := ![4,28,33,34,6,15,0,7,5,27,14,30,31,32,18,8,16,17,10,12,13,29,1,2,3,9,11,25,22,35,26,19,20,23,24,21,36,37]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide,by decide⟩

private def sym8 : Aut := by
  let f : V → V := ![0,5,7,2,1,4,8,9,3,6]
  let g : V → V := ![0,4,3,8,5,1,9,2,6,7]
  let a : R → R := ![4,5,19,20,6,22,0,7,28,27,35,30,2,3,21,1,36,37,29,23,24,10,8,31,32,9,11,25,15,14,26,33,34,12,13,18,16,17]
  let b : R → R := ![6,15,12,13,0,1,4,7,22,25,21,26,33,34,29,28,36,37,35,2,3,14,5,19,20,27,30,9,8,18,11,23,24,31,32,10,16,17]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide,by decide⟩

private def sym9 : Aut := by
  let f : V → V := ![0,5,7,9,4,1,8,2,6,3]
  let g : V → V := ![0,5,7,9,4,1,8,2,6,3]
  let a : R → R := ![6,15,33,34,4,28,0,7,22,25,35,26,12,13,29,1,36,37,21,31,32,18,8,23,24,9,11,27,5,14,30,19,20,2,3,10,16,17]
  let b : R → R := ![6,15,33,34,4,28,0,7,22,25,35,26,12,13,29,1,36,37,21,31,32,18,8,23,24,9,11,27,5,14,30,19,20,2,3,10,16,17]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide,by decide⟩

private def sym10 : Aut := by
  let f : V → V := ![0,5,8,3,4,1,7,6,2,9]
  let g : V → V := ![0,5,8,3,4,1,7,6,2,9]
  let a : R → R := ![6,22,19,20,4,5,0,7,15,25,14,26,23,24,10,8,16,17,18,2,3,21,1,12,13,9,11,27,28,35,30,33,34,31,32,29,36,37]
  let b : R → R := ![6,22,19,20,4,5,0,7,15,25,14,26,23,24,10,8,16,17,18,2,3,21,1,12,13,9,11,27,28,35,30,33,34,31,32,29,36,37]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide,by decide⟩

private def sym11 : Aut := by
  let f : V → V := ![0,5,8,6,1,4,7,3,9,2]
  let g : V → V := ![0,4,9,7,5,1,3,6,2,8]
  let a : R → R := ![4,28,33,34,6,15,0,7,5,27,14,30,31,32,18,8,16,17,10,12,13,29,1,2,3,9,11,25,22,35,26,19,20,23,24,21,36,37]
  let b : R → R := ![6,22,23,24,0,8,4,7,15,25,18,26,19,20,10,5,16,17,14,31,32,35,28,33,34,27,30,9,1,21,11,12,13,2,3,29,36,37]
  exact ⟨⟨a,b,by decide,by decide⟩,⟨f,g,by decide,by decide⟩,by decide,by decide,by decide⟩

def group : Fin 12 → Aut := ![sym0,sym1,sym2,sym3,sym4,sym5,sym6,sym7,sym8,sym9,sym10,sym11]

def choice : V → V → Fin 12 := ![![0,0,0,4,4,5,2,5,7,6],![0,0,0,0,0,1,2,1,2,3],![0,0,0,0,4,5,0,1,0,1],![4,0,0,4,4,10,2,4,8,4],![4,0,4,4,4,8,6,11,8,6],![5,1,5,10,8,5,7,5,7,9],![2,2,0,2,6,7,2,3,2,3],![5,1,1,4,11,5,3,5,5,9],![7,2,0,8,8,7,2,5,7,6],![6,3,1,4,6,9,3,9,6,6]]

def first : V → V → V := ![![0,0,0,0,0,0,0,0,0,0],![0,1,1,1,1,1,1,1,1,1],![0,1,2,2,1,1,2,2,2,2],![0,1,2,2,1,1,2,2,2,2],![0,1,1,1,1,1,1,1,1,1],![0,1,1,1,1,1,1,1,1,1],![0,1,2,2,1,1,2,2,2,2],![0,1,2,2,1,1,2,2,2,2],![0,1,2,2,1,1,2,2,2,2],![0,1,2,2,1,1,2,2,2,2]]

def second : V → V → V := ![![0,1,2,2,1,1,2,2,2,2],![1,1,2,3,4,4,2,3,3,3],![2,2,2,3,3,3,6,3,8,8],![2,3,3,2,2,3,8,8,3,6],![1,4,3,2,1,4,3,3,3,2],![1,4,3,3,4,1,3,2,2,3],![2,2,6,8,3,3,2,8,3,3],![2,3,3,8,3,2,8,2,6,3],![2,3,8,3,3,2,3,6,2,8],![2,3,8,6,2,3,3,3,8,2]]

def reps : List (V × V) := [(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,6),(2,8)]

def pick (i j : V) : Aut := group (choice i j)
theorem witness (i j : V) (ne : i ≠ j) :
    ((first i j,second i j)∈reps) ∧
     (((pick i j).vertex i=first i j ∧ (pick i j).vertex j=second i j) ∨
      ((pick i j).vertex j=first i j ∧ (pick i j).vertex i=second i j)) := by
  revert i j; decide +kernel

theorem primary_act (a : Aut) (i : V) : act a.row (word i) = word (a.vertex i) :=
  (act_eq_iff ..).mpr (a.primary i)
theorem target_act (a : Aut) : act a.row label = label := (act_eq_iff ..).mpr a.target
theorem pivot_act (a : Aut) : act a.row (word 0) = word 0 := by rw [primary_act,a.fixes]
#print axioms witness
end PetersenPhysicalRowGroup
