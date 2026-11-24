import PetersenNineProjected
import PetersenPositiveCheck
open PetersenFrontier PetersenFrontierSearch PetersenWordCost PetersenPhysicalWords PetersenDominantPin
namespace PetersenElevenCofactors
set_option maxRecDepth 24000
set_option maxHeartbeats 0
abbrev smallTarget := PetersenNineData.label
abbrev src := PetersenNineProjected.basis
abbrev suffix := ∀ o ∈ PetersenNineOrbit.outputs, PetersenNinePositive.Blocked 14 (o :: PetersenNineData.sources)
private theorem constants : (0 : BitVec 24) ∈ src ∧ (~~~0 : BitVec 24) ∈ src := by decide
def row0 : Fin 24 → Fin 38 := ![2,19,23,1,8,12,17,14,5,21,18,26,22,10,15,11,7,36,31,35,33,28,29,30]
private theorem small0 (nine : suffix) : PetersenPhysicalProjection.NoPhysical src (PetersenPackedPin.project row0 target) 15 := by
  have e : PetersenPackedPin.project row0 target = smallTarget := by decide +kernel
  rw [e]
  exact PetersenNineProjected.small nine
def row1 : Fin 24 → Fin 38 := ![5,28,33,2,12,19,26,21,4,27,25,37,31,18,23,17,9,30,15,29,22,6,10,11]
private theorem small1 (nine : suffix) : PetersenPhysicalProjection.NoPhysical src (PetersenPackedPin.project row1 target) 15 := by
  have e : PetersenPackedPin.project row1 target = smallTarget := by decide +kernel
  rw [e]
  exact PetersenNineProjected.small nine
def row2 : Fin 24 → Fin 38 := ![4,28,31,0,8,6,11,7,5,27,10,30,33,18,15,17,14,37,23,35,22,19,25,26]
private theorem small2 (nine : suffix) : PetersenPhysicalProjection.NoPhysical src (PetersenPackedPin.project row2 target) 15 := by
  have e : PetersenPackedPin.project row2 target = smallTarget := by decide +kernel
  rw [e]
  exact PetersenNineProjected.small nine
def row3 : Fin 24 → Fin 38 := ![2,19,23,1,8,12,16,14,5,21,18,26,22,10,15,11,7,36,31,35,33,28,29,30]
private theorem small3 (nine : suffix) : PetersenPhysicalProjection.NoPhysical src (PetersenPackedPin.project row3 target) 15 := by
  have e : PetersenPackedPin.project row3 target = smallTarget := by decide +kernel
  rw [e]
  exact PetersenNineProjected.small nine
def row4 : Fin 24 → Fin 38 := ![2,19,23,1,8,12,16,14,5,21,18,26,22,10,15,11,7,37,31,35,33,28,29,30]
private theorem small4 (nine : suffix) : PetersenPhysicalProjection.NoPhysical src (PetersenPackedPin.project row4 target) 15 := by
  have e : PetersenPackedPin.project row4 target = smallTarget := by decide +kernel
  rw [e]
  exact PetersenNineProjected.small nine
def state0 : List (BitVec 38) := [0x1,0x250b122259,0x844004183,0x3020203a0e,0x481b442c,0x142408b0,0x60408cc0,0x181870f00,0x60607f000,0x3807f80000,0x3ff8000000]
theorem excluded0 (nine : suffix) : ∀ m ≤ 17, ∀ c, ¬ Tail Plain state0.toFinset m c {target} := by
  intro m le c
  exact PetersenPositiveCheck.sound row0 (small0 nine) constants (p := []) (by decide +kernel) le
def state1 : List (BitVec 38) := [0x2000002208,0x250b122259,0x844004183,0x3020203a0e,0x481b442c,0x142408b0,0x60408cc0,0x181870f00,0x60607f000,0x3807f80000,0x3ff8000000]
theorem excluded1 (nine : suffix) : ∀ m ≤ 17, ∀ c, ¬ Tail Plain state1.toFinset m c {target} := by
  intro m le c
  exact PetersenPositiveCheck.sound row0 (small0 nine) constants (p := []) (by decide +kernel) le
def state2 : List (BitVec 38) := [0x2,0x250b122259,0x844004183,0x3020203a0e,0x481b442c,0x142408b0,0x60408cc0,0x181870f00,0x60607f000,0x3807f80000,0x3ff8000000]
theorem excluded2 (nine : suffix) : ∀ m ≤ 17, ∀ c, ¬ Tail Plain state2.toFinset m c {target} := by
  intro m le c
  exact PetersenPositiveCheck.sound row1 (small1 nine) constants (p := []) (by decide +kernel) le
def state3 : List (BitVec 38) := [0xc,0x250b122259,0x844004183,0x3020203a0e,0x481b442c,0x142408b0,0x60408cc0,0x181870f00,0x60607f000,0x3807f80000,0x3ff8000000]
theorem excluded3 (nine : suffix) : ∀ m ≤ 17, ∀ c, ¬ Tail Plain state3.toFinset m c {target} := by
  intro m le c
  exact PetersenPositiveCheck.sound row2 (small2 nine) constants (p := []) (by decide +kernel) le
def state4 : List (BitVec 38) := [0x1,0x250b122259,0x844004183,0x3020203a0e,0x481b442c,0x142408b0,0x60408cc0,0x181870f00,0x60607f000,0x3807f80000,0x3ff8000000,0x1af4eddda6]
theorem excluded4 (nine : suffix) : ∀ m ≤ 17, ∀ c, ¬ Tail Plain state4.toFinset m c {target} := by
  intro m le c
  exact PetersenPositiveCheck.sound row3 (small3 nine) constants (p := []) (by decide +kernel) le
def state5 : List (BitVec 38) := [0x2d4f1263db,0x250b122259,0x844004183,0x3020203a0e,0x481b442c,0x142408b0,0x60408cc0,0x181870f00,0x60607f000,0x3807f80000,0x3ff8000000,0x1af4eddda6]
theorem excluded5 (nine : suffix) : ∀ m ≤ 17, ∀ c, ¬ Tail Plain state5.toFinset m c {target} := by
  intro m le c
  exact PetersenPositiveCheck.sound row3 (small3 nine) constants (p := []) (by decide +kernel) le
def state6 : List (BitVec 38) := [0x2000002208,0x250b122259,0x844004183,0x3020203a0e,0x481b442c,0x142408b0,0x60408cc0,0x181870f00,0x60607f000,0x3807f80000,0x3ff8000000,0x1af4eddda6]
theorem excluded6 (nine : suffix) : ∀ m ≤ 17, ∀ c, ¬ Tail Plain state6.toFinset m c {target} := by
  intro m le c
  exact PetersenPositiveCheck.sound row3 (small3 nine) constants (p := []) (by decide +kernel) le
def state7 : List (BitVec 38) := [0x352b323a5f,0x250b122259,0x844004183,0x3020203a0e,0x481b442c,0x142408b0,0x60408cc0,0x181870f00,0x60607f000,0x3807f80000,0x3ff8000000,0x1af4eddda6]
theorem excluded7 (nine : suffix) : ∀ m ≤ 17, ∀ c, ¬ Tail Plain state7.toFinset m c {target} := by
  intro m le c
  exact PetersenPositiveCheck.sound row3 (small3 nine) constants (p := []) (by decide +kernel) le
def state8 : List (BitVec 38) := [0x1af4eddda7,0x250b122259,0x844004183,0x3020203a0e,0x481b442c,0x142408b0,0x60408cc0,0x181870f00,0x60607f000,0x3807f80000,0x3ff8000000]
theorem excluded8 (nine : suffix) : ∀ m ≤ 17, ∀ c, ¬ Tail Plain state8.toFinset m c {target} := by
  intro m le c
  exact PetersenPositiveCheck.sound row3 (small3 nine) constants (p := []) (by decide +kernel) le
def state9 : List (BitVec 38) := [0x1af4eddda7,0x250b122259,0x844004183,0x3020203a0e,0x481b442c,0x142408b0,0x60408cc0,0x181870f00,0x60607f000,0x3807f80000,0x3ff8000000,0x1af4eddda6]
theorem excluded9 (nine : suffix) : ∀ m ≤ 17, ∀ c, ¬ Tail Plain state9.toFinset m c {target} := by
  intro m le c
  exact PetersenPositiveCheck.sound row3 (small3 nine) constants (p := []) (by decide +kernel) le
def state10 : List (BitVec 38) := [0x1020201806,0x250b122259,0x844004183,0x3020203a0e,0x481b442c,0x142408b0,0x60408cc0,0x181870f00,0x60607f000,0x3807f80000,0x3ff8000000]
theorem excluded10 (nine : suffix) : ∀ m ≤ 17, ∀ c, ¬ Tail Plain state10.toFinset m c {target} := by
  intro m le c
  exact PetersenPositiveCheck.sound row2 (small2 nine) constants (p := []) (by decide +kernel) le
def state11 : List (BitVec 38) := [0x1020201806,0x250b122259,0x844004183,0x3020203a0e,0x481b442c,0x142408b0,0x60408cc0,0x181870f00,0x60607f000,0x3807f80000,0x3ff8000000,0x1af4eddda6]
theorem excluded11 (nine : suffix) : ∀ m ≤ 17, ∀ c, ¬ Tail Plain state11.toFinset m c {target} := by
  intro m le c
  exact PetersenPositiveCheck.sound row3 (small3 nine) constants (p := []) (by decide +kernel) le
def state12 : List (BitVec 38) := [0x3af4edffae,0x250b122259,0x844004183,0x3020203a0e,0x481b442c,0x142408b0,0x60408cc0,0x181870f00,0x60607f000,0x3807f80000,0x3ff8000000]
theorem excluded12 (nine : suffix) : ∀ m ≤ 17, ∀ c, ¬ Tail Plain state12.toFinset m c {target} := by
  intro m le c
  exact PetersenPositiveCheck.sound row4 (small4 nine) constants (p := []) (by decide +kernel) le
def state13 : List (BitVec 38) := [0x3af4edffae,0x250b122259,0x844004183,0x3020203a0e,0x481b442c,0x142408b0,0x60408cc0,0x181870f00,0x60607f000,0x3807f80000,0x3ff8000000,0x1af4eddda6]
theorem excluded13 (nine : suffix) : ∀ m ≤ 17, ∀ c, ¬ Tail Plain state13.toFinset m c {target} := by
  intro m le c
  exact PetersenPositiveCheck.sound row3 (small3 nine) constants (p := []) (by decide +kernel) le
#print axioms excluded0
end PetersenElevenCofactors
