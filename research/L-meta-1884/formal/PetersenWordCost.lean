import PetersenPhysicalBoundary
import Std.Tactic.BVDecide

open PetersenSignedBridge
namespace PetersenWordCost

def read {w : Nat} (a : BitVec w) : Func (Fin w) := fun i => a.getLsbD i.val

theorem read_inj {w : Nat} {a b : BitVec w} (h : read a = read b) : a = b :=
  BitVec.eq_of_getLsbD_eq (fun i hi => congrFun h ⟨i,hi⟩)

def Covered {w} (W : List (BitVec w)) (a : BitVec w) : Prop := a ∈ 0 :: W ∨ ~~~a ∈ 0 :: W

def gate {w} (op : Bool) (a b : BitVec w) := if op then a ||| b else a &&& b

theorem pack_av {w} {S : List (BitVec w)} {f} (h : Av (S.map read) f) :
    ∃ a, Covered S a ∧ read a = f := by
  induction h with
  | wire hm =>
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
    exact ⟨x, Or.inl (List.mem_cons_of_mem _ hx),rfl⟩
  | zero => exact ⟨0, Or.inl (by simp), by funext i; simp [read]⟩
  | one => exact ⟨~~~0, Or.inr (by simp), by funext i; simp [read,i.isLt]⟩
  | neg h ih =>
    obtain ⟨x,hx,rfl⟩ := ih
    refine ⟨~~~x, ?_, by funext i; simp [read,i.isLt]⟩
    rcases hx with h | h
    · exact Or.inr (by simpa using h)
    · exact Or.inl h

inductive Packed {w} (I : List (BitVec w)) : Nat → List (BitVec w) → Prop where
  | start : Packed I 0 I
  | step {k W a b} (r : Packed I k W) (ha : Covered W a) (hb : Covered W b) (op : Bool) :
      Packed I (k+1) (gate op a b :: W)

theorem pack_run {w} {I : List (BitVec w)} {k W} (r : Run (I.map read) k W) :
    ∃ S, Packed I k S ∧ S.map read = W := by
  induction r with
  | start => exact ⟨I,.start,rfl⟩
  | and r ha hb ih =>
    obtain ⟨S,rs,rfl⟩ := ih
    obtain ⟨a,hca,rfl⟩ := pack_av ha
    obtain ⟨b,hcb,rfl⟩ := pack_av hb
    refine ⟨_,.step rs hca hcb false,?_⟩
    rw [List.map_cons]
    apply congrArg (fun h => h :: S.map read)
    funext i
    simp [gate,read]
  | or r ha hb ih =>
    obtain ⟨S,rs,rfl⟩ := ih
    obtain ⟨a,hca,rfl⟩ := pack_av ha
    obtain ⟨b,hcb,rfl⟩ := pack_av hb
    refine ⟨_,.step rs hca hcb true,?_⟩
    rw [List.map_cons]
    apply congrArg (fun h => h :: S.map read)
    funext i
    simp [gate,read]

/-- The finite word query quantifies over the two actual operand truth tables at each gate. -/
def Reject {w} (t : BitVec w) : Nat → List (BitVec w) → Prop
  | 0, W => ¬ Covered W t
  | k+1, W => ∀ a b : BitVec w, Covered W a → Covered W b → ∀ op : Bool,
       Reject t k (gate op a b :: W)

theorem Packed.after {w} {I S : List (BitVec w)} {k} (r : Packed I k S) (t : BitVec w) :
    ∀ d, Reject t (k+d) I → Reject t d S := by
  induction r with
  | start => intro d h;simpa using h
  | @step k W a b r ha hb op ih =>
    intro d h
    have hs : Reject t (d+1) W := ih (d+1) (by convert h using 1; omega)
    exact hs a b ha hb op

theorem reject_covered {w} {t : BitVec w} : ∀ {k W}, Reject t k W → ¬ Covered W t := by
  intro k
  induction k with
  | zero => exact fun h => h
  | succ k ih =>
    intro W h ht
    have hz : Covered W 0 := Or.inl (by simp)
    have bad := ih (h 0 0 hz hz false)
    apply bad
    rcases ht with a | b
    · exact Or.inl (by simp only [List.mem_cons] at *; tauto)
    · exact Or.inr (by simp only [List.mem_cons] at *; tauto)

/-- A lower bound in the original signed function-DAG semantics, with constants and free complements. -/
def NoAtMost {w} (I : List (BitVec w)) (t : BitVec w) (K : Nat) : Prop :=
  ∀ k ≤ K, ∀ W, Run (I.map read) k W → ¬ Av W (read t)

theorem lower_of_reject {w} {I : List (BitVec w)} {t : BitVec w} {K} (h : Reject t K I) :
    NoAtMost I t K := by
  intro k hk W run output
  obtain ⟨S,rs,rfl⟩ := pack_run run
  obtain ⟨a,ha,eq⟩ := pack_av output
  have hs := rs.after t (K-k) (by simpa [Nat.add_sub_of_le hk] using h)
  exact (reject_covered hs) (read_inj eq ▸ ha)

def pack {w : Nat} (f : Fin w → Bool) : BitVec w :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)

theorem read_pack {w : Nat} (f : Fin w → Bool) : read (pack f) = f := by
  funext i
  simp only [read, pack, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD, i.isLt]

def inputs (n : Nat) : List (BitVec (2^n)) :=
  List.ofFn (fun i : Fin n => pack (fun x : Fin (2^n) => x.val.testBit i.val))

def graphTarget (n : Nat) (edges : List (Nat × Nat)) : BitVec (2^n) :=
  pack (fun x => edges.any (fun (a,b) => x.val.testBit a && x.val.testBit b))

end PetersenWordCost
