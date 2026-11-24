import PetersenAntichain
import PetersenDominantPin
import PetersenPhysicalCut
import PetersenNinePositive
open PetersenAntichain PetersenDominantPin PetersenMonotoneFrontier PetersenFrontier
open PetersenPhysicalWords PetersenPhysicalCut PetersenWordCost PetersenFrontierSearch

namespace PetersenAntiStep
variable {w : Nat}
local notation "W" => BitVec w

theorem physical {t a b o : W} {I : List W} (g : CleanGate t I.toFinset a b o) :
    o ∉ (0::I).toFinset ∧ WordGate (0:W) a b o := by
  have absent : ¬ Avail I.toFinset o := fun e => g.2 o e (PetersenMonotoneFrontier.refl t _)
  have norm : key (0:W) o = o := by
    rw [key,ite_eq_right (fun e => absent (Or.inr (Or.inl e)))]
  refine ⟨?_,?_⟩
  · intro m; simp only [List.toFinset_cons,Finset.mem_insert] at m
    exact absent (m.imp_right (fun e => Or.inr e))
  · obtain ⟨op,eq⟩ := g.1
    have lit (x : W) : x∈literals (0:W) x := by
      unfold literals; split
      · rename_i e; subst x; exact List.mem_cons_self ..
      · exact List.mem_cons_self ..
    apply List.mem_flatMap.mpr
    refine ⟨(a,b),List.mem_product.mpr ⟨lit _,lit _⟩,?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    cases op
    · left; change o=a&&&b at eq; rw [←eq,norm]
    · right; change o=a|||b at eq; rw [←eq,norm]

theorem fits_ok {I L : List W} {t : W} {m c} (neg : List (Fin w))
    (tail : ATail t I.toFinset L.toFinset m c {t}) : fits 0 t neg L = true := by
  exact fits_tail (I := (0::I).toFinset) (by simp) L (PetersenNinePositive.tailGate (fun _ _ _ g => physical g) tail.toTail) neg

theorem count {t : W} {I A T : Finset W} {m c} (tail : ATail t I A m c T) :
    A.card+c = T.card+m := by
  induction tail with
  | nil => simp
  | @step K a b o m c T _ ne fresh _ g tail ih =>
    have h : o ∉ K := fun p => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem p))
    by_cases ha : a∈K <;> by_cases hb : b∈K <;>
      simp [ha,hb,h,ne,credit,Finset.card_insert_of_notMem] at * <;> omega

def freshB (I L : List W) (t o : W) : Bool :=
  !(0::(~~~0)::(I++L)).any (betterB t o)

theorem fresh_ok {I L : List W} {t o a b : W}
    (old : ∀ x ∈ L.toFinset, ¬ Better t o x)
    (gate : CleanGate t I.toFinset a b o) : freshB I L t o = true := by
  unfold freshB
  cases e : (0 :: ~~~0 :: (I++L)).any (betterB t o) with
  | false => rfl
  | true =>
    obtain ⟨x,h,v⟩ := List.any_eq_true.mp e
    have bet := (better_spec ..).mp v
    simp only [List.mem_cons,List.mem_append] at h
    rcases h with rfl|rfl|h|h
    · exact False.elim (gate.2 _ (Or.inl rfl) bet)
    · exact False.elim (gate.2 _ (Or.inr (Or.inl rfl)) bet)
    · exact False.elim (gate.2 _ (Or.inr (Or.inr (List.mem_toFinset.mpr h))) bet)
    · exact False.elim (old x (List.mem_toFinset.mpr h) bet)

def localMoves (I L : List W) (t : W) (neg : List (Fin w)) (spare : Nat) (a b : W) : List (List W) :=
  [false,true].flatMap fun op =>
    let o := gate op a b
    if freshB I L t o then
      [false,true].flatMap fun ka => [false,true].filterMap fun kb =>
        let K := kept L a b ka kb
        let N := o::K
        if ka.toNat+kb.toNat ≤ spare && !(K.any fun x => betterB t x o) && fits 0 t neg N then some N else none
    else []

def moves (I L : List W) (t : W) (neg : List (Fin w)) (spare : Nat) : List (List W) :=
  L.flatMap fun a => L.flatMap fun b => if a.toNat < b.toNat then localMoves I L t neg spare a b else []

private theorem one {I L : List W} {t a b o : W} {K : Finset W} {spare m c}
    (neg : List (Fin w)) (old : L.toFinset=insert a (insert b K))
    (fresh : o ∉ L.toFinset) (no : ∀x∈L.toFinset,¬Better t o x) (g : CleanGate t I.toFinset a b o)
    (tail : ATail t I.toFinset (insert o K) m c {t}) (le : credit a b K ≤ spare) :
    ∃ V∈localMoves I L t neg spare a b, V.toFinset=insert o K := by
  let ka := decide (a∈K)
  let kb := decide (b∈K)
  let N := o :: kept L a b ka kb
  have kk : (kept L a b ka kb).toFinset=K := kept_eq old
  have eq : N.toFinset=insert o K := by simp only [N,List.toFinset_cons,kk]
  obtain ⟨op,h⟩ := g.1
  have ft := fresh_ok no g
  have bits (v : Bool) : v∈[false,true] := by cases v <;> simp
  have co : ka.toNat+kb.toNat ≤ spare := by
    by_cases ha : a∈K <;> by_cases hb : b∈K <;> simpa [ka,kb,ha,hb,credit] using le
  have incomparable : (kept L a b ka kb).any (fun x => betterB t x o) = false := by
    cases e : (kept L a b ka kb).any (fun x => betterB t x o) with
    | false => rfl
    | true =>
      obtain ⟨x,hx,bet⟩ := List.any_eq_true.mp e
      have xk : x ∈ K := kk ▸ List.mem_toFinset.mpr hx
      have same := tail.liveAnti x (Finset.mem_insert_of_mem xk) o (Finset.mem_insert_self ..) ((better_spec ..).mp bet)
      have notK : o∉K := fun p => fresh (old ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem p))
      exact False.elim (notK (same ▸ xk))
  have feasible := fits_ok neg (eq ▸ tail)
  refine ⟨N,?_,eq⟩
  apply List.mem_flatMap.mpr
  refine ⟨op,bits op,?_⟩
  rw [←h]; simp only [ft,ite_true]
  apply List.mem_flatMap.mpr
  refine ⟨ka,bits ka,List.mem_filterMap.mpr ⟨kb,bits kb,?_⟩⟩
  change _ = true at feasible
  dsimp only [N] at feasible
  simp [co,incomparable,N]
  exact feasible

def Blocked (I : List W) (t : W) (fuel : Nat) (L : List W) : Prop :=
  ∀ m ≤ fuel, ∀ c, ¬ ATail t I.toFinset L.toFinset m c {t}

theorem split {I L : List W} {t : W} {d : Nat} (neg : List (Fin w)) (missing : t ∉ L.toFinset)
    (done : ∀ V∈moves I L t neg (d+2-L.toFinset.card), Blocked I t d V) :
    Blocked I t (d+1) L := by
  intro m hm c tail
  have acc := count tail
  simp only [Finset.card_singleton] at acc
  generalize old : L.toFinset = S at tail
  generalize stop : ({t} : Finset W) = T at tail
  cases tail with
  | nil => exact missing ((old.trans stop.symm) ▸ Finset.mem_singleton_self _)
  | @step K a b o m c T _ ne fr no g tail =>
    have ends : ATail t I.toFinset (insert o K) m c {t} := stop.symm ▸ tail
    have am : a∈L := List.mem_toFinset.mp (old ▸ Finset.mem_insert_self ..)
    have bm : b∈L := List.mem_toFinset.mp (old ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have fresh : o∉L.toFinset := old ▸ fr
    have absent : ∀x∈L.toFinset,¬Better t o x := old ▸ no
    have lt : a.toNat ≠ b.toNat := fun h => ne (BitVec.eq_of_toNat_eq h)
    have advance {x y : W} (hx : x∈L) (hy : y∈L) (xy : x.toNat < y.toNat)
        (eq : L.toFinset=insert x (insert y K)) (gate : CleanGate t I.toFinset x y o)
        (creditOK : credit x y K ≤ d+2-L.toFinset.card) : False := by
      obtain ⟨V,mem,e⟩ := one neg eq fresh absent gate ends creditOK
      apply done V (List.mem_flatMap.mpr ⟨x,hx,List.mem_flatMap.mpr ⟨y,hy,by simpa only [xy,ite_true] using mem⟩⟩) m (by omega) c (e ▸ ends)
    rcases lt_or_gt_of_ne lt with h|h
    · exact advance am bm h old g (by omega)
    · apply advance bm am h (by simpa only [Finset.insert_comm b a] using old) _ _
      · refine ⟨?_,g.2⟩; obtain ⟨op,eq⟩ := g.1; use op
        cases op <;> simpa [PetersenWordCost.gate,BitVec.and_comm,BitVec.or_comm] using eq
      · have swap : credit b a K = credit a b K := by simp only [credit,Nat.add_comm]
        rw [swap]; omega

#print axioms split
end PetersenAntiStep
