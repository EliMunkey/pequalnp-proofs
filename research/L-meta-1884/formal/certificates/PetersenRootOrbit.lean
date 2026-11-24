import PetersenVerifiedGroup
open PetersenWordCost PetersenPackedFrontier PetersenFrontier PetersenFrontierSearch
open PetersenLayerCheck PetersenFrontierSymmetry PetersenVerifiedGroup
namespace PetersenRootOrbit
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
variable {w : Nat}

/-- A root-pair exclusion considers either sign, either connective, and every
legal last-use pattern for the two operands. -/
def DeadPair (t : BitVec w) (fuel : Nat) (I : Finset (BitVec w)) (a b : BitVec w) : Prop :=
  ∀ (K : Finset (BitVec w)) o m c, I = insert a (insert b K) → a ≠ b → o ∉ I →
    signedWordGate a b o → m+1 ≤ fuel → ¬Tail signedWordGate (insert o K) m c {t}

theorem pair_transport {hw : 0<w} (p : Fin w ≃ Fin w) (fix : p ⟨0,hw⟩=⟨0,hw⟩)
    {t : BitVec w} (eqt : act p t=t) {I : Finset (BitVec w)} (eqI : I.map (rowEmb p)=I)
    {a b} {k} (h : DeadPair t k I (act p a) (act p b)) : DeadPair t k I a b := by
  intro K o m c hK ne new gate hm run
  have moved := tail_map (rowEmb p) (fun _ _ _ g => gate_fold p fix g) run
  have ht : rowEmb p t = t := eqt
  rw [Finset.map_insert,Finset.map_singleton,ht] at moved
  have start : I = insert (act p a) (insert (act p b) (K.map (rowEmb p))) := by
    conv_lhs => rw [←eqI,hK]
    simp only [Finset.map_insert]; rfl
  have fresh : act p o ∉ I := by
    intro m; apply new
    have mem : rowEmb p o ∈ I.map (rowEmb p) := by rw [eqI]; exact m
    simpa using mem
  exact h _ _ _ _ start (fun q => ne (act_injective p q)) fresh (gate_fold p fix gate) hm moved

theorem base_preserved {n : Nat} (p : Fin n ≃ Fin n) :
    (inputs n).toFinset.map (rowEmb (vertexRows p))=(inputs n).toFinset := by
  ext v
  simp only [Finset.mem_map,List.mem_toFinset,inputs,List.mem_ofFn]
  constructor
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨p i,(act_coordinate p i).symm⟩
  · rintro ⟨i,rfl⟩
    refine ⟨coordinate (p.symm i),⟨_,rfl⟩,?_⟩
    change act (vertexRows p) (coordinate (p.symm i)) = coordinate i
    simp [act_coordinate]

def singleRow (i : Fin 10) : Fin 1024 := (BitVec.ofNat 10 (2^i.val)).toFin

theorem target_not_primary : graphWord E ∉ (inputs 10).toFinset := by
  intro h
  obtain ⟨i,eq⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp h)
  change coordinate i = graphWord E at eq
  have hc : read (coordinate i) (singleRow i)=true := by
    rw [coordinate,read_pack]; revert i; decide
  have hg : read (graphWord E) (singleRow i)=false := by
    unfold graphWord graphTarget; rw [read_pack]; revert i; decide
  rw [eq,hg] at hc
  exact Bool.noConfusion hc

/-- For any gate budget, ruling out the two concrete first-input pairs suffices
for the complete signed Petersen frontier. No root symmetry is assumed. -/
theorem two_pairs (fuel : Nat)
    (edge : DeadPair (graphWord E) fuel (inputs 10).toFinset (coordinate 0) (coordinate 1))
    (apart : DeadPair (graphWord E) fuel (inputs 10).toFinset (coordinate 0) (coordinate 2)) :
    Blocked (graphWord E) fuel (inputs 10) := by
  intro m hm c tr
  generalize start : (inputs 10).toFinset = I at tr
  generalize ending : ({graphWord E} : Finset (BitVec 1024)) = T at tr
  cases tr with
  | nil =>
    exact target_not_primary ((start.trans ending.symm) ▸ Finset.mem_singleton_self _)
  | @step K a b o m c T ne fresh g tail =>
    have am : a ∈ (inputs 10).toFinset := start ▸ Finset.mem_insert_self ..
    have bm : b ∈ (inputs 10).toFinset := start ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    obtain ⟨i,ae⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp am)
    obtain ⟨j,be⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp bm)
    change coordinate i=a at ae
    change coordinate j=b at be
    subst a; subst b
    have distinct : i ≠ j := by rintro rfl; exact ne rfl
    let p := (signed i j).toEquiv
    have wit := signed_pair i j distinct
    have representative : DeadPair (graphWord E) fuel (inputs 10).toFinset
        (act (vertexRows p) (coordinate i)) (act (vertexRows p) (coordinate j)) := by
      rw [act_coordinate,act_coordinate]
      change DeadPair _ _ _ (coordinate ((signed i j).toEquiv i)) (coordinate ((signed i j).toEquiv j))
      rw [wit.1,wit.2]
      split
      · exact edge
      · exact apart
    have no := pair_transport (vertexRows p) (vertexRows_zero p) (stable_target (signed i j))
      (base_preserved p) representative
    exact no _ _ _ _ start ne (start ▸ fresh) g (by omega) (ending.symm ▸ tail)

#print axioms two_pairs
end PetersenRootOrbit
