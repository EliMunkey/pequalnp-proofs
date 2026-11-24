import PetersenPackedFrontier
import PetersenForwardSearch

open PetersenSignedBridge PetersenFrontier PetersenPackedFrontier PetersenWordCost

namespace PetersenPhysicalWords
variable {w : Nat}

def key (p v : BitVec w) : BitVec w := if v = ~~~p then p else v

def literals (p v : BitVec w) : List (BitVec w) :=
  if v = p then [p,~~~p] else [v]

private theorem source (p a : BitVec w) : a ∈ literals p (key p a) := by
  by_cases h : a = ~~~p
  · rw [h]; simp [key,literals]
  · simp only [key,ite_eq_right h]
    by_cases eq : a = p <;> simp [literals,eq]

private theorem key_related {p a b : BitVec w} (h : key p a = key p b) : a=b ∨ a = ~~~b := by
  by_cases ha : a = ~~~p <;> by_cases hb : b = ~~~p <;> simp_all [key]

def choices (p a b : BitVec w) : List (BitVec w) :=
  ((literals p a).product (literals p b)).flatMap fun (x,y) => [key p (x &&& y),key p (x ||| y)]

def WordGate (p a b o : BitVec w) := o ∈ choices p a b

private theorem gate_key (p : BitVec w) (op : Bool) (a b : BitVec w) :
    WordGate p (key p a) (key p b) (key p (PetersenWordCost.gate op a b)) := by
  apply List.mem_flatMap.mpr
  refine ⟨(a,b),List.mem_product.mpr ⟨source p a,source p b⟩,?_⟩
  cases op <;> simp [PetersenWordCost.gate]

inductive Positive (I : List (BitVec w)) : Nat → List (BitVec w) → Prop where
  | start : Positive I 0 I
  | add {k W a b} (op : Bool) : Positive I k W → a ∈ W → b ∈ W →
    Positive I (k+1) (PetersenWordCost.gate op a b :: W)

def hot (a : BitVec w) : Prop := a ≠ 0 ∧ a ≠ ~~~0

private theorem ordinary {a b : BitVec w} (op : Bool) (h : hot (PetersenWordCost.gate op a b))
    (freshA : PetersenWordCost.gate op a b ≠ a) (freshB : PetersenWordCost.gate op a b ≠ b) :
    hot a ∧ hot b ∧ ¬(a=b ∨ a = ~~~b) := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,?_⟩
  · rintro rfl; cases op <;> simp_all [PetersenWordCost.gate,hot]
  · rintro rfl; cases op <;> simp_all [PetersenWordCost.gate,hot]
  · rintro rfl; cases op <;> simp_all [PetersenWordCost.gate,hot]
  · rintro rfl; cases op <;> simp_all [PetersenWordCost.gate,hot]
  · rintro (rfl|rfl) <;> cases op <;> simp_all [PetersenWordCost.gate,hot]

theorem positive_prefix {raw : List (BitVec w)} {k W} (r : Positive raw k W)
    (p : BitVec w) (I : Finset (BitVec w)) (initial : ∀ v ∈ raw, hot v → key p v ∈ I) :
    ∃ m ≤ k, ∃ S, Prefix (WordGate p) I m S ∧ ∀ v ∈ W, hot v → key p v ∈ S := by
  induction r with
  | start => exact ⟨0,le_rfl,I,Prefix.start,initial⟩
  | @add k W a b op _ ha hb ih =>
    obtain ⟨m,hm,S,t,cov⟩ := ih
    let o := PetersenWordCost.gate op a b
    by_cases make : hot o ∧ key p o ∉ S
    · have na : o ≠ a := fun e => make.2 (e ▸ cov _ ha (e ▸ make.1))
      have nb : o ≠ b := fun e => make.2 (e ▸ cov _ hb (e ▸ make.1))
      obtain ⟨aa,bb,ne⟩ := ordinary op make.1 na nb
      have s := Prefix.add t (cov _ ha aa) (cov _ hb bb) (fun h => ne (key_related h)) make.2
        (gate_key p op a b)
      refine ⟨m+1,by omega,_,s,?_⟩
      intro v h hv
      rcases List.mem_cons.mp h with rfl|old
      · exact Finset.mem_insert_self ..
      · exact Finset.mem_insert_of_mem (cov _ old hv)
    · refine ⟨m,by omega,S,t,?_⟩
      intro v h hv
      rcases List.mem_cons.mp h with rfl|old
      · by_contra no; exact make ⟨hv,no⟩
      · exact cov _ old hv

/-- Sample any physical program on an arbitrary finite list of assignments. -/
theorem sample {X : Type} (r : Fin w → X) {init W : List (Func X)} {k}
    (src : Direct init k W) :
    Positive (init.map (fun f => pack (f ∘ r))) k (W.map (fun f => pack (f ∘ r))) := by
  induction src with
  | start => exact Positive.start
  | and _ ha hb ih =>
    simp only [List.map_cons]
    have q := Positive.add false ih (List.mem_map.mpr ⟨_,ha,rfl⟩) (List.mem_map.mpr ⟨_,hb,rfl⟩)
    convert q using 2
    exact pack_bin false _ _
  | or _ ha hb ih =>
    simp only [List.map_cons]
    have q := Positive.add true ih (List.mem_map.mpr ⟨_,ha,rfl⟩) (List.mem_map.mpr ⟨_,hb,rfl⟩)
    convert q using 2
    exact pack_bin true _ _

def row (j : Fin 38) : PInput := PhysicalBoundary.word (PhysicalBoundary.selected.get j)
def table (f : Func PInput) : BitVec 38 := pack (f ∘ row)
def input : List (BitVec 38) := base.map table
def pivot : BitVec 38 := table (vertex 0)
def target : BitVec 38 := table PetersenTarget

private theorem raw_ok : (rails.map table).all (fun v =>
    v == 0 || v == ~~~0 || input.contains (key pivot v)) = true := by decide
private theorem target_key : key pivot target = target := by decide
private theorem target_hot : hot target := by unfold hot; decide

/-- Every original physical circuit reaches the 38-row target in a word frontier, using the
    complement solely at reads of the marked primary and excluding regenerated primary words. -/
theorem boundary_coverage {k W} (src : Direct rails k W) (output : PetersenTarget ∈ W) :
    ∃ U ⊆ input.toFinset, ∃ m ≤ k, ∃ c,
    Trace (fun a b o => o ∉ input.toFinset ∧ WordGate pivot a b o) U m c {target} ∧
      m+1 = U.card+c := by
  have s := sample row src
  obtain ⟨j,hj,S,p,cov⟩ := positive_prefix s pivot input.toFinset (by
    intro v hv h
    have h' := List.all_eq_true.mp raw_ok v hv
    have ne := h.1
    have nz := h.2
    have h'' := Bool.or_eq_true_iff.mp h'
    rcases h'' with h | h
    · rcases Bool.or_eq_true_iff.mp h with h | h
      · exact (ne (beq_iff_eq.mp h)).elim
      · exact (nz (beq_iff_eq.mp h)).elim
    · exact List.mem_toFinset.mpr (List.contains_iff_mem.mp h))
  have tar := cov target (List.mem_map.mpr ⟨_,output,rfl⟩) target_hot
  rw [target_key] at tar
  obtain ⟨U,hi,m,hm,c,t⟩ := p.no_input_output.schedule {target} (Finset.singleton_subset_iff.mpr tar)
  exact ⟨U,hi,m,by omega,c,t,t.sink⟩

end PetersenPhysicalWords
