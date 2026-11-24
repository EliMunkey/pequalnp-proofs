import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3039_444
  (extract : ∀ (N G : ℕ) (a : (Σ _ : Fin N, Fin N) → Finset (Fin G))
    (s : Finset (Σ _ : Fin N, Fin N)), 44 * (s.biUnion a).card < s.card →
    ∃ t ⊆ s, t.card = 44 * (t.biUnion a).card + 1 ∧
    ∀ b ⊆ t.biUnion a, b.Nonempty →
        44 * b.card < (t.filter fun e => ¬Disjoint (a e) b).card)
  (obstruction : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   let x5 : ℕ := x2 + x2;   (2 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) →           PEqualNP.MetaComplexity.IsMinimalMonoCircuit x5 x4 →             (∀ (x11 : Finset (Fin x2)), x11.card ≤ x1 → x4.eval (PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet x3 x11) x11) = Bool.false) →               let x12 : List ℕ := x4.lineDegrees x5 (Finset.Ico x2 x5);               have x13 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => if x13.op.eval [] = Bool.true ∧ x13.inputs.length = (2 : ℕ) ∧ (x13.inputs.all fun (x14 : ℕ) => Decidable.decide ((0 : ℕ) < x12.getD x14 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x13) x4.gates, output := x4.output : PEqualNP.CircuitLowerBounds.Circuit };               have x14 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x14 x15 : Fin x2) => PEqualNP.EdgeOwnership.pairInput (Fin.castAdd x2 x14) (Fin.natAdd x2 x15);               have x15 : ℕ → (Fin x5 → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal x5 x4;               have x16 : (_ : Fin x2) × Fin x2 → Finset (Fin x4.size) := fun (x16 : (_ : Fin x2) × Fin x2) => {x17 : Fin x4.size | (x15 ↑x17 fun (x18 : Fin x5) => Bool.false) = Bool.false ∧ x15 (↑x17) (x14 x16.snd x16.fst) = Bool.true};               ∀ (x17 : Finset ((_ : Fin x2) × Fin x2)), (∀ x18 ∈ x17, x18.snd ∈ x3 x18.fst ∧ x4.eval (List.ofFn (x14 x18.snd x18.fst)) > x13.eval (List.ofFn (x14 x18.snd x18.fst))) → x17.Nonempty → (∀ x20 ⊆ x17.biUnion x16, x20.Nonempty → (44 : ℕ) * x20.card < {x23 ∈ x17 | ¬Disjoint (x16 x23) x20}.card) → False) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (2 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →             have x11 : Finset (Fin x2) → Fin (x2 + x2) → Bool := fun (x11 : Finset (Fin x2)) (x12 : Fin (x2 + x2)) => Fin.addCases (fun (x13 : Fin x2) => Decidable.decide ¬∃ x14 ∈ x11, x3 x13 x14) (fun (x13 : Fin x2) => Decidable.decide (x13 ∈ x11)) x12;             (∀ (x12 : Finset (Fin x2)), x12.card ≤ x1 → x5.eval (List.ofFn (x11 x12)) = Bool.false) →               have x13 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => if x13.op.eval [] = Bool.true ∧ x13.inputs.length = (2 : ℕ) ∧ (x13.inputs.all fun (x14 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x14 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x13) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };               have x14 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x14 x15 : Fin x2) (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x14 ∨ x16 = Fin.natAdd x2 x15);               ∀ (x15 : Fin x2 → Finset (Fin x2)), (∀ (x16 x17 : Fin x2), x17 ∈ x15 x16 → x3 x17 x16 ∧ x5.eval (List.ofFn (x14 x17 x16)) = Bool.true ∧ x13.eval (List.ofFn (x14 x17 x16)) = Bool.false) → ∑ x17 : Fin x2, (x15 x17).card ≤ (44 : ℕ) * Fintype.card { x17 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x17) Bool.false = Bool.false ∧ ∃ (x18 : Fin x2), ∃ x19 ∈ x15 x18, (x5.wires (List.ofFn (x14 x19 x18))).getD (x2 + x2 + ↑x17) Bool.false = Bool.true } := by

  classical
  intro q n inc inst c hq hn hline hjoin hmin maxInput hs d pair t ht
  let s := (Finset.univ : Finset (Fin n)).sigma t
  have hzero : List.ofFn (fun _ : Fin (n+n) => false) = List.replicate (n+n) false := by simp
  let a := fun (e : Σ _ : Fin n, Fin n) => Finset.univ.filter fun j : Fin c.size =>
      PEqualNP.EdgeOwnership.gateVal (n+n) c j.val (fun _ => false) = false ∧
      PEqualNP.EdgeOwnership.gateVal (n+n) c j.val (pair e.2 e.1) = true
  have hc : s.card = ∑ l, (t l).card := Finset.card_sigma _ _
  have hu : s.biUnion a = Finset.univ.filter (fun j : Fin c.size =>
      (c.wires (List.replicate (n+n) false)).getD (n+n+j.val) false = false ∧
      ∃ l, ∃ p ∈ t l, PEqualNP.EdgeOwnership.gateVal (n+n) c j.val (pair p l) = true) := by
    ext j
    simp only [s, a, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_sigma]
    delta PEqualNP.EdgeOwnership.gateVal
    simp only [hzero]
    constructor
    · rintro ⟨⟨l,p⟩, hm, hzero, hone⟩
      exact ⟨hzero,l,p,hm,hone⟩
    · rintro ⟨hzero,l,p,hm,hone⟩
      exact ⟨⟨l,p⟩,hm,hzero,hone⟩
  rw [Fintype.card_subtype]
  change (∑ l, (t l).card) ≤ 44 * (Finset.univ.filter _).card
  rw [← hc]
  change s.card ≤ 44 * (Finset.univ.filter (fun j : Fin c.size =>
      (c.wires (List.replicate (n+n) false)).getD (n+n+j.val) false = false ∧
      ∃ l, ∃ p ∈ t l, PEqualNP.EdgeOwnership.gateVal (n+n) c j.val (pair p l) = true)).card
  rw [← hu]
  by_contra! bad
  obtain ⟨u, hus, hsize, hexpand⟩ := extract n c.size a s bad
  let S := fun l : Fin n => Finset.univ.filter (fun p : Fin n => inc p l)
  have col (l : Fin n) : (S l).card = q + 1 := by
    simpa only [S, Fintype.card_subtype] using hline l
  have jn (p r : Fin n) (hne : p ≠ r) : ∃! l, p ∈ S l ∧ r ∈ S l := by
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hjoin p r hne
  have hneg (Y : Finset (Fin n)) (hy : Y.card ≤ q) :
      c.eval (PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet S Y) Y) = false := by
    have eqinput :
        PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet S Y) Y =
          List.ofFn (maxInput Y) := by
      rw [List.ofFn_add]
      delta PEqualNP.GenericRejection.incidenceInput
      congr 1
      · apply congrArg List.ofFn
        funext p
        change decide _ = Fin.addCases _ _ (Fin.castAdd n p)
        rw [Fin.addCases_left]
        delta PEqualNP.GenericRejection.zeroSet
        simp [S]
      · apply congrArg List.ofFn
        funext l
        change decide _ = Fin.addCases _ _ (Fin.natAdd n l)
        rw [Fin.addCases_right]
    rw [eqinput]
    exact hs Y hy
  apply obstruction q n S c hq hn col jn hmin hneg u _ (Finset.card_pos.mp (by omega)) hexpand
  intro e he
  obtain ⟨hI, hon, hoff⟩ := ht e.1 e.2 (Finset.mem_sigma.mp (hus he)).2
  exact ⟨by simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hI, by change c.eval (List.ofFn (pair e.2 e.1)) > d.eval (List.ofFn (pair e.2 e.1)); rw [hon, hoff]; decide⟩
