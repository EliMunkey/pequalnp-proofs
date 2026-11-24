import PetersenFastNode
import PetersenFastPin
open PetersenLayerCheck PetersenPackedPin PetersenFastPin PetersenWordCost
namespace PetersenBank
variable {w n : Nat}
structure View (w n : Nat) where
  size : Nat
  rows : Fin size → Fin w
  inputs : List (BitVec size)
  budget : Nat
  cache : Fin n → Option (BitVec size)

def tableOK (p : View w n) (word : Fin n → BitVec w) : Bool :=
  (List.finRange n).all fun i => match p.cache i with
    | none => true
    | some b => b == project p.rows (word i)

theorem valid_table {p : View w n} {word : Fin n → BitVec w} (yes : tableOK p word = true) :
    PetersenFastPin.valid p.rows word p.cache := by
  intro i
  have atI := List.all_eq_true.mp yes i (by simp)
  cases e : p.cache i with
  | none => trivial
  | some v => simpa [e] using atI

def Sound (p : View w n) (word : Fin n → BitVec w) (t : BitVec w) : Prop :=
  NoAtMost p.inputs (project p.rows t) p.budget ∧ forcedConst p.rows t = false ∧
  PetersenFastPin.valid p.rows word p.cache

def check (views : Array (View w n)) (word : Fin n → BitVec w)
    (program : Nat → List Instr) (ids : Nat → List (Fin n)) (why : Nat → Nat × Nat)
    (fuel i : Nat) : Bool :=
  let (c,pr) := why i
  match views[c]? with
  | some p => quick word p.cache p.inputs p.budget (program pr) (ids i) fuel
  | none => false

theorem check_sound {views : Array (View w n)} {word : Fin n → BitVec w} {t : BitVec w}
    (base : ∀ p∈views.toList, Sound p word t)
    {program : Nat → List Instr} {ids : Nat → List (Fin n)} {why : Nat → Nat × Nat} {fuel i : Nat}
    (h : check views word program ids why fuel i = true) : Blocked t fuel ((ids i).map word) := by
  unfold check at h
  cases eq : views[(why i).1]? with
  | none => simp [eq] at h
  | some p =>
    have pb : p ∈ views.toList := by
      have mem := Array.mem_of_getElem? eq
      simpa using mem
    obtain ⟨small,hot,vals⟩ := base p pb
    apply quick_sound vals small hot
    simpa [eq] using h

theorem children {views : Array (View w n)} {word : Fin n → BitVec w} {t : BitVec w}
    (base : ∀ p∈views.toList, Sound p word t)
    {program : Nat → List Instr} {ids : Nat → List (Fin n)} {why : Nat → Nat × Nat} {fuel : Nat}
    {live : Array Nat} {more : List Nat}
    (test : live.toList.all (fun i => more.contains i || check views word program ids why fuel i) = true)
    (done : ∀ i∈more, Blocked t fuel ((ids i).map word)) :
    ∀ V∈(live.map fun i => (ids i).map word).toList, Blocked t fuel V := by
  intro V mem
  simp only [Array.toList_map,List.mem_map] at mem
  obtain ⟨i,hi,rfl⟩ := mem
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp test i hi) with h|h
  · exact done i (List.contains_iff_mem.mp h)
  · exact check_sound base h

end PetersenBank
