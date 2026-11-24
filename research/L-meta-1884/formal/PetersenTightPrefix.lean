import PetersenShortPrefix
open PetersenFrontier PetersenWordCost PetersenSignalCut PetersenShortPrefix
namespace PetersenTightPrefix
variable {w : Nat}

def masks (tight : Bool) : List Bool := if tight then [true] else [false,true]

def tightExclude (ops : V w → V w → List (V w)) (t : V w) (neg : List (Fin w)) :
    Nat → Nat → List (V w) → Bool
  | depth, fuel, L =>
    if !viable L t neg fuel then true else
    if L.contains t then false else
    match depth, fuel with
    | 0, _ => false
    | _, 0 => true
    | n+1,k+1 => L.all fun a => L.all fun b =>
        a == b || (ops a b).all fun o =>
          L.contains o || (masks (L.toFinset.card == k+2)).all fun da => (masks (L.toFinset.card == k+2)).all fun db =>
            tightExclude ops t neg n k (successor L a b o da db)


theorem tight_sound {G : V w → V w → V w → Prop} (locality : Local G)
    (ops : V w → V w → List (V w)) (complete : ∀ a b o, G a b o → o ∈ ops a b)
    (t : V w) (neg : List (Fin w)) (depth : Nat) :
    ∀ {I m fuel} (L : List (V w)), L.toFinset = I → m ≤ fuel → Tail G I m {t} →
      tightExclude ops t neg depth fuel L ≠ true := by
  induction depth with
  | zero =>
    intro I m fuel L eq le r
    have cap := tail_capacity r
    have card : L.toFinset.card ≤ fuel+1 := by rw [eq];simp at cap;omega
    have good : viable L t neg fuel = true := Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true card,separates_of_tail locality r L eq neg⟩
    simp [tightExclude,good]
  | succ d ih =>
    intro I m fuel L eq le r bad
    have cap := tail_capacity r
    have card : L.toFinset.card ≤ fuel+1 := by rw [eq];simp at cap;omega
    have good : viable L t neg fuel = true := Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true card,separates_of_tail locality r L eq neg⟩
    by_cases done : t ∈ L
    · cases fuel <;> simp [tightExclude,good,done] at bad
    cases r with
    | done =>
      apply done
      apply List.mem_toFinset.mp
      rw [eq]
      simp
    | @more K a b o m Z ab fresh hg tail =>
      cases fuel with
      | zero => omega
      | succ k =>
        have step :
            (L.all fun a => L.all fun b =>
            a == b || (ops a b).all fun o =>
              L.contains o || (masks (L.toFinset.card == k+2)).all fun da => (masks (L.toFinset.card == k+2)).all fun db =>
                tightExclude ops t neg d k (successor L a b o da db)) = true := by
          simpa [tightExclude,good,done] using bad
        have ma : a ∈ L := List.mem_toFinset.mp (eq.symm ▸ (by simp : a ∈ insert a (insert b K)))
        have mb : b ∈ L := List.mem_toFinset.mp (eq.symm ▸ (by simp : b ∈ insert a (insert b K)))
        have be := List.all_eq_true.mp (List.all_eq_true.mp step a ma) b mb
        have different : (a==b) = false := beq_eq_false_iff_ne.mpr ab
        simp only [different,Bool.false_or] at be
        have oe := List.all_eq_true.mp be o (complete _ _ _ hg)
        have unused : o ∉ L := fun h => fresh (eq ▸ List.mem_toFinset.mpr h)
        simp only [List.contains_eq_mem,decide_eq_false unused,Bool.false_or] at oe
        have valid : decide (a ∉ K) ∈ masks (L.toFinset.card == k+2) ∧
            decide (b ∉ K) ∈ masks (L.toFinset.card == k+2) := by
          by_cases tight : L.toFinset.card = k+2
          · have nc : o ∉ K := fun x => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem x))
            have bound := tail_capacity tail
            rw [Finset.card_insert_of_notMem nc] at bound
            simp only [Finset.card_singleton] at bound
            rw [eq] at tight
            have na : a ∉ K := by
              intro ak
              have ak' : a ∈ insert b K := Finset.mem_insert_of_mem ak
              rw [Finset.insert_eq_of_mem ak'] at tight
              have q := Finset.card_insert_le b K
              omega
            have nb : b ∉ K := by
              intro bk
              rw [Finset.insert_eq_of_mem bk] at tight
              have q := Finset.card_insert_le a K
              omega
            simp [masks, eq, tight, na, nb]
          · cases ha : decide (a ∉ K) <;> cases hb : decide (b ∉ K) <;> simp [masks,tight,ha,hb]
        have fail := List.all_eq_true.mp (List.all_eq_true.mp oe (decide (a ∉ K)) valid.1) (decide (b ∉ K)) valid.2
        exact ih _ (choose_retire o ab eq) (by omega) tail fail


#print axioms tight_sound
end PetersenTightPrefix
