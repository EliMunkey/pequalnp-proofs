import PetersenLayerCheck
open PetersenSignedBridge PetersenFrontier PetersenWordCost PetersenPackedFrontier PetersenFrontierSearch PetersenLayerCheck
namespace PetersenFrontierSymmetry

variable {w : Nat}

/-- Transport the truth table by an actual permutation of its assignment rows. -/
def act (p : Fin w ≃ Fin w) (v : BitVec w) : BitVec w := pack (read v ∘ p)

theorem read_act (p : Fin w ≃ Fin w) (v : BitVec w) : read (act p v) = read v ∘ p := read_pack _

theorem act_injective (p : Fin w ≃ Fin w) : Function.Injective (act p) := by
  intro a b eq
  apply read_inj; funext i
  have same := congrFun (congrArg read eq) (p.symm i)
  simpa only [read_act,Function.comp_apply,Equiv.apply_symm_apply] using same

def rowEmb (p : Fin w ≃ Fin w) : BitVec w ↪ BitVec w := ⟨act p,act_injective p⟩

theorem act_not (p : Fin w ≃ Fin w) (v : BitVec w) : act p (~~~v) = ~~~(act p v) := by
  apply read_inj
  calc
    read (act p (~~~v)) = read (~~~v) ∘ p := read_act p _
    _ = PetersenFrontier.flip (read v ∘ p) := by
      funext i; simp [PetersenWordCost.read,PetersenFrontier.flip,(p i).isLt]
    _ = read (~~~act p v) := by
      rw [← read_act]; funext i; simp [PetersenFrontier.flip,PetersenWordCost.read,i.isLt]

theorem act_and (p : Fin w ≃ Fin w) (a b : BitVec w) : act p (a &&& b) = act p a &&& act p b := by
  calc
    act p (a &&& b) = pack (bin false (read a ∘ p) (read b ∘ p)) := by
      unfold act; congr 1; funext i; simp [PetersenWordCost.read,bin]
    _ = _ := pack_bin false _ _

theorem act_or (p : Fin w ≃ Fin w) (a b : BitVec w) : act p (a ||| b) = act p a ||| act p b := by
  calc
    act p (a ||| b) = pack (bin true (read a ∘ p) (read b ∘ p)) := by
      unfold act; congr 1; funext i; simp [PetersenWordCost.read,bin]
    _ = _ := pack_bin true _ _

theorem act_norm {hw : 0<w} (p : Fin w ≃ Fin w) (fix0 : p ⟨0,hw⟩=⟨0,hw⟩) (v : BitVec w) :
    act p (norm v) = norm (act p v) := by
  have e := congrFun (read_act p v) ⟨0,hw⟩
  simp only [Function.comp_apply,fix0] at e
  change (act p v).getLsbD 0 = v.getLsbD 0 at e
  cases h : v.getLsbD 0 <;> simp [norm,e,h,act_not]

theorem gate_fold {hw : 0<w} (p : Fin w ≃ Fin w) (fix0 : p ⟨0,hw⟩=⟨0,hw⟩)
    {a b o} (g : signedWordGate a b o) : signedWordGate (act p a) (act p b) (act p o) := by
  obtain ⟨⟨x,y⟩,hxy,hout⟩ := List.mem_flatMap.mp g
  obtain ⟨hx,hy⟩ := List.mem_product.mp hxy
  have lit {u v : BitVec w} (h : u ∈ [v,~~~v]) : act p u ∈ [act p v,~~~act p v] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    rcases h with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr (act_not p _)
  refine List.mem_flatMap.mpr ⟨(act p x,act p y),List.mem_product.mpr ⟨lit hx,lit hy⟩,?_⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hout ⊢
  rcases hout with rfl|rfl
  · exact Or.inl ((act_norm p fix0 _).trans (congrArg norm (act_and p x y)))
  · exact Or.inr ((act_norm p fix0 _).trans (congrArg norm (act_or p x y)))

theorem tail_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    {G : α → α → α → Prop} {H : β → β → β → Prop} (e : α ↪ β)
    (preserve : ∀ a b o, G a b o → H (e a) (e b) (e o)) {I W m c}
    (r : Tail G I m c W) : Tail H (I.map e) m c (W.map e) := by
  induction r with
  | nil => exact Tail.nil _
  | @step K a b o m c T ne fresh g _ ih =>
    simp only [Finset.map_insert] at ih ⊢
    have fresh' : e o ∉ insert (e a) (insert (e b) (K.map e)) := by
      simpa only [←Finset.map_insert,Finset.mem_map'] using fresh
    have cr : credit (e a) (e b) (K.map e) = credit a b K := by simp [credit]
    rw [← cr]
    exact Tail.step (fun q => ne (e.injective q)) fresh' (preserve _ _ _ g) ih

/-- A checked representative rejects its complete orbit. Reindexing can be used at
any layer. The predicate includes the gate budget and preserves arbitrary fan-out. -/
theorem blocked_of_orbit {hw : 0<w} (p : Fin w ≃ Fin w) (fix0 : p ⟨0,hw⟩=⟨0,hw⟩)
    {t : BitVec w} (symmetry : act p t = t) {L V : List (BitVec w)} (fuel : Nat)
    (matchState : L.toFinset.map (rowEmb p) = V.toFinset)
    (closed : Blocked t fuel V) : Blocked t fuel L := by
  intro m hm c tail
  have moved := tail_map (rowEmb p) (fun _ _ _ g => gate_fold p fix0 g) tail
  have eq : (rowEmb p) t = t := symmetry
  rw [matchState,Finset.map_singleton,eq] at moved
  exact closed m hm c moved


theorem act_inverse (p : Fin w ≃ Fin w) (v : BitVec w) : act p.symm (act p v) = v := by
  apply read_inj
  funext i
  have e := congrFun (read_act p.symm (act p v)) i
  simpa only [Function.comp_apply,read_act,Equiv.apply_symm_apply] using e

theorem act_zero (p : Fin w ≃ Fin w) : act p (0 : BitVec w) = 0 := by
  apply read_inj; rw [read_act]; funext i
  simp [PetersenWordCost.read]

/-- Relabel the full cube's assignment indices by a permutation of the base
vertices. This constructor is accompanied by explicit inverse and zero laws. -/
def vertexRows {n : Nat} (p : Fin n ≃ Fin n) : Fin (2^n) ≃ Fin (2^n) where
  toFun x := (act p (BitVec.ofFin x)).toFin
  invFun x := (act p.symm (BitVec.ofFin x)).toFin
  left_inv x := by simp [act_inverse]
  right_inv x := by
    simp only [BitVec.ofFin_toFin]
    have e := act_inverse p.symm (BitVec.ofFin x)
    simpa using congrArg BitVec.toFin e

@[simp] theorem vertexRows_zero {n : Nat} (p : Fin n ≃ Fin n) :
    vertexRows p 0 = 0 := by
  change (act p (0 : BitVec n)).toFin = 0
  rw [act_zero]; rfl

/-- A transport equation can be checked pointwise on the graph's input masks,
without reducing a whole arbitrary packed truth table to normal form. -/
theorem act_eq_iff (p : Fin w ≃ Fin w) (a b : BitVec w) :
    act p a = b ↔ ∀ j, read a (p j) = read b j := by
  constructor
  · intro h j
    have e := congrFun (read_act p a) j
    simpa [h] using e.symm
  · intro h; apply read_inj; rw [read_act]; exact funext h

def coordinate {n : Nat} (i : Fin n) : BitVec (2^n) :=
  pack (fun j : Fin (2^n) => j.val.testBit i.val)

/-- A compiler can transport each intermediate from its defining gates after
rewriting the primary labels just once using this equation. -/
theorem act_coordinate {n : Nat} (p : Fin n ≃ Fin n) (i : Fin n) :
    act (vertexRows p) (coordinate i) = coordinate (p i) := by
  rw [act_eq_iff]; intro x
  simp only [coordinate,read_pack]
  have e := congrFun (read_act p (BitVec.ofFin x)) i
  exact e


def Adj {n : Nat} (E : List (Fin n × Fin n)) (i j : Fin n) : Prop := (i,j) ∈ E ∨ (j,i) ∈ E

def graphWord {n : Nat} (E : List (Fin n × Fin n)) : BitVec (2^n) :=
  graphTarget n (E.map (fun e => (e.1.val,e.2.val)))

theorem graph_iff {n : Nat} (E : List (Fin n × Fin n)) (x : Fin (2^n)) :
    read (graphWord E) x = true ↔ ∃ i j, Adj E i j ∧ x.val.testBit i.val = true ∧
      x.val.testBit j.val = true := by
  simp only [graphWord,graphTarget,read_pack,List.any_map,List.any_eq_true,
    Function.comp_apply,Bool.and_eq_true]
  constructor
  · rintro ⟨⟨i,j⟩,h,hi,hj⟩
    exact ⟨i,j,Or.inl h,hi,hj⟩
  · rintro ⟨i,j,h|h,hi,hj⟩
    · exact ⟨(i,j),h,hi,hj⟩
    · exact ⟨(j,i),h,hj,hi⟩

theorem assignment_bit {n : Nat} (p : Fin n ≃ Fin n) (x : Fin (2^n)) (i : Fin n) :
    (vertexRows p x).val.testBit i.val = x.val.testBit (p i).val :=
  congrFun (read_act p (BitVec.ofFin x)) i

/-- Verifying a graph automorphism needs only the finite adjacency matrix
on vertices; it certifies symmetry on every assignment at once. -/
theorem graph_invariant {n : Nat} (E : List (Fin n × Fin n)) (p : Fin n ≃ Fin n)
    (pres : ∀ i j, Adj E (p i) (p j) ↔ Adj E i j) :
    act (vertexRows p) (graphWord E) = graphWord E := by
  rw [act_eq_iff]
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [graph_iff,graph_iff]
  constructor
  · rintro ⟨i,j,edge,a,b⟩
    exact ⟨p i,p j,(pres i j).mpr edge,(assignment_bit p x i) ▸ a,(assignment_bit p x j) ▸ b⟩
  · rintro ⟨i,j,edge,a,b⟩
    refine ⟨p.symm i,p.symm j,(pres _ _).mp (by simpa using edge),?_,?_⟩
    · simpa only [assignment_bit,Equiv.apply_symm_apply] using a
    · simpa only [assignment_bit,Equiv.apply_symm_apply] using b

#print axioms graph_invariant
#print axioms act_coordinate
#print axioms blocked_of_orbit
end PetersenFrontierSymmetry
