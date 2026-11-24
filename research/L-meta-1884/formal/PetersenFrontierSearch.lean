import PetersenPackedFrontier

open PetersenSignedBridge PetersenWordCost PetersenFrontier PetersenPackedFrontier
namespace PetersenFrontierSearch

section Tail
variable {α : Type*} [DecidableEq α]

inductive Tail (G : α → α → α → Prop) : Finset α → Nat → Nat → Finset α → Prop where
  | nil (W : Finset α) : Tail G W 0 0 W
  | step {K a b o m c T} : a ≠ b → o ∉ insert a (insert b K) → G a b o →
      Tail G (insert o K) m c T →
      Tail G (insert a (insert b K)) (m+1) (credit a b K+c) T

theorem tail_prepend {G : α → α → α → Prop} {I L T m c d s}
    (p : Trace G I m c L) (q : Tail G L d s T) : Tail G I (m+d) (c+s) T := by
  induction p generalizing d s with
  | start => simpa using q
  | step _ hab fresh g ih =>
    have v := ih (Tail.step hab fresh g q)
    convert v using 1 <;> omega

theorem to_tail {G : α → α → α → Prop} {I L m c} (p : Trace G I m c L) :
    Tail G I m c L := by simpa using tail_prepend p (Tail.nil L)

end Tail

variable {w : Nat}
abbrev B := BitVec w

def consistent (t : BitVec w) : List (BitVec w) → BitVec w → Bool
  | [], r => r &&& t == 0 || r &&& (~~~t) == 0
  | x::W,r => r &&& t == 0 || r &&& (~~~t) == 0 ||
      (consistent t W (r &&& x) && consistent t W (r &&& (~~~x)))

theorem nonzero_witness {a : BitVec w} (h : a ≠ 0) : ∃ i : Fin w, PetersenWordCost.read a i = true := by
  by_contra! no
  apply h
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  have := no ⟨n,hn⟩
  simpa [PetersenWordCost.read] using this

theorem consistent_complete (t : BitVec w) (W : List (BitVec w)) (r : BitVec w)
    (det : ∀ i j : Fin w, PetersenWordCost.read r i = true → PetersenWordCost.read r j = true →
      (∀ x ∈ W, PetersenWordCost.read x i = PetersenWordCost.read x j) →
      PetersenWordCost.read t i = PetersenWordCost.read t j) : consistent t W r = true := by
  induction W generalizing r with
  | nil =>
    simp only [consistent,Bool.or_eq_true,beq_iff_eq]
    by_cases h : r &&& t = 0
    · exact Or.inl h
    · right; by_contra h'
      obtain ⟨i,hi⟩ := nonzero_witness h
      obtain ⟨j,hj⟩ := nonzero_witness h'
      simp [PetersenWordCost.read,i.isLt,j.isLt] at hi hj
      have eq := det i j hi.1 hj.1 (by simp)
      simp [PetersenWordCost.read,hi.2,hj.2] at eq
  | cons x W ih =>
    apply Bool.or_eq_true_iff.mpr; right
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply ih; intro i j hi hj rest
      simp [PetersenWordCost.read] at hi hj
      exact det i j hi.1 hj.1 (by
        intro a ha; rcases List.mem_cons.mp ha with rfl|h
        · exact hi.2.trans hj.2.symm
        · exact rest a h)
    · apply ih; intro i j hi hj rest
      simp [PetersenWordCost.read,i.isLt,j.isLt] at hi hj
      exact det i j hi.1 hj.1 (by
        intro a ha; rcases List.mem_cons.mp ha with rfl|h
        · exact hi.2.trans hj.2.symm
        · exact rest a h)

theorem gate_agrees {a b o : BitVec w} (g : signedWordGate a b o) {i j : Fin w}
    (ha : PetersenWordCost.read a i = PetersenWordCost.read a j)
    (hb : PetersenWordCost.read b i = PetersenWordCost.read b j) :
    PetersenWordCost.read o i = PetersenWordCost.read o j := by
  obtain ⟨⟨p,q⟩,hp,ho⟩ := List.mem_flatMap.mp g
  obtain ⟨hp,hq⟩ := List.mem_product.mp hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp hq ho
  rcases hp with rfl|rfl <;> rcases hq with rfl|rfl <;> rcases ho with rfl|rfl <;>
    unfold norm <;> split <;>
    simp [PetersenWordCost.read,i.isLt,j.isLt] at ha hb ⊢ <;> simp [ha,hb]

theorem tail_agree {I T : Finset (BitVec w)} {m c} (t : Tail signedWordGate I m c T)
    (i j : Fin w) : (∀ x ∈ I, PetersenWordCost.read x i = PetersenWordCost.read x j) →
      ∀ x ∈ T, PetersenWordCost.read x i = PetersenWordCost.read x j := by
  induction t with
  | nil => exact id
  | @step K a b o m c T _ _ gate _ ih =>
    intro initial; apply ih; intro x hx
    rcases Finset.mem_insert.mp hx with rfl|h
    · exact gate_agrees gate (initial _ (Finset.mem_insert_self ..))
        (initial _ (Finset.mem_insert_of_mem (Finset.mem_insert_self ..)))
    · exact initial _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))

def kept (L : List (BitVec w)) (a b : BitVec w) (ka kb : Bool) : List (BitVec w) :=
  L.filter fun x => (ka || x != a) && (kb || x != b)

theorem kept_eq {L : List (BitVec w)} {a b} {K : Finset (BitVec w)}
    (h : L.toFinset = insert a (insert b K)) :
    (kept L a b (decide (a ∈ K)) (decide (b ∈ K))).toFinset = K := by
  ext x
  have live : x ∈ L ↔ x = a ∨ x = b ∨ x ∈ K := by
    rw [← List.mem_toFinset,h]; simp
  simp only [kept,List.mem_toFinset,List.mem_filter,Bool.and_eq_true,Bool.or_eq_true,
    decide_eq_true_eq,bne_iff_ne,live]
  by_cases ha : x=a <;> by_cases hb : x=b <;> aesop

def moves (L : List (BitVec w)) (budget : Nat) : List (BitVec w × List (BitVec w) × Nat) :=
  L.flatMap fun a => L.flatMap fun b => if b.toNat ≤ a.toNat then [] else
    (options a b).eraseDups.flatMap fun o =>
      if L.contains o then [] else
        [false,true].flatMap fun ka => [false,true].filterMap fun kb =>
          let cost := ka.toNat+kb.toNat
          if cost ≤ budget then some (o,o :: kept L a b ka kb,cost) else none

private theorem move_covers_ordered {L : List (BitVec w)} {K : Finset (BitVec w)} {a b o}
    (old : L.toFinset = insert a (insert b K)) (lt : a.toNat < b.toNat) (fresh : o ∉ L.toFinset)
    (g : signedWordGate a b o) {budget} (h : credit a b K ≤ budget) :
    ∃ N, (o,N,credit a b K) ∈ moves L budget ∧ N.toFinset = insert o K := by
  let ka := decide (a ∈ K)
  let kb := decide (b ∈ K)
  have cost : ka.toNat+kb.toNat = credit a b K := by
    by_cases ha : a∈K <;> by_cases hb : b∈K <;> simp [ha,hb,credit,ka,kb]
  have am : a ∈ L := List.mem_toFinset.mp (old ▸ Finset.mem_insert_self ..)
  have bm : b ∈ L := List.mem_toFinset.mp (old ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
  refine ⟨o::kept L a b ka kb,?_,?_⟩
  · simp only [moves,List.mem_flatMap]
    refine ⟨a,am,b,bm,?_⟩
    rw [if_neg (Nat.not_le.mpr lt)]
    apply List.mem_flatMap.mpr
    refine ⟨o,List.mem_eraseDups.mpr g,?_⟩
    have om : L.contains o = false := by simpa using fresh
    simp only [om,Bool.false_eq_true,↓reduceIte,List.mem_flatMap]
    refine ⟨ka,by cases ka <;> simp,?_⟩
    apply List.mem_filterMap.mpr
    exact ⟨kb,by cases kb <;> simp,by simp [cost,h]⟩
  · simp only [List.toFinset_cons,ka,kb,kept_eq old]

theorem gate_swap {a b o : BitVec w} (g : signedWordGate a b o) : signedWordGate b a o := by
  obtain ⟨⟨p,q⟩,hp,h⟩ := List.mem_flatMap.mp g
  obtain ⟨p1,p2⟩ := List.mem_product.mp hp
  refine List.mem_flatMap.mpr ⟨(q,p),List.mem_product.mpr ⟨p2,p1⟩,?_⟩
  simpa only [BitVec.and_comm q p, BitVec.or_comm q p] using h

theorem move_covers {L : List (BitVec w)} {K : Finset (BitVec w)} {a b o}
    (old : L.toFinset = insert a (insert b K)) (ne : a ≠ b) (fresh : o ∉ L.toFinset)
    (g : signedWordGate a b o) {budget} (h : credit a b K ≤ budget) :
    ∃ N, (o,N,credit a b K) ∈ moves L budget ∧ N.toFinset = insert o K := by
  by_cases lt : a.toNat < b.toNat
  · exact move_covers_ordered old lt fresh g h
  · have lt' : b.toNat < a.toNat := by
      have diff : a.toNat ≠ b.toNat := fun eq => ne (BitVec.eq_of_toNat_eq eq)
      omega
    have swap : credit a b K = credit b a K := by simp only [credit,Nat.add_comm]
    rw [swap] at h ⊢
    apply move_covers_ordered (a := b) (b := a) (K := K) _ lt' fresh (gate_swap g) h
    simpa only [Finset.insert_comm] using old

def search (t : BitVec w) : Nat → Nat → List (BitVec w) → Bool
  | 0,_,L => L.contains t
  | d+1,c,L => L.contains t || (consistent t L (~~~0) &&
      (moves L c).any fun (_,N,s) => search t d (c-s) N)

theorem search_complete {L : List (BitVec w)} {t : BitVec w} {m c}
    (tail : Tail signedWordGate L.toFinset m c {t}) {d cap} (depth : m≤d) (budget : c≤cap) :
    search t d cap L = true := by
  induction d generalizing L m c cap with
  | zero =>
    have : m=0 := by omega
    subst m
    generalize e : L.toFinset = S at tail
    generalize et : ({t} : Finset (BitVec w)) = T at tail
    cases tail
    have ht : t ∈ L.toFinset := (e.trans et.symm) ▸ Finset.mem_singleton_self _
    simpa [search] using (List.mem_toFinset.mp ht)
  | succ d ih =>
    simp only [search,Bool.or_eq_true]
    by_cases done : t ∈ L
    · exact Or.inl (by simpa using done)
    right; apply Bool.and_eq_true_iff.mpr
    constructor
    · apply consistent_complete
      intro i j _ _ h
      exact tail_agree tail i j (fun x hx => h x (List.mem_toFinset.mp hx)) _ (Finset.mem_singleton_self _)
    · generalize e : L.toFinset = S at tail
      generalize et : ({t} : Finset (BitVec w)) = T at tail
      cases tail with
      | nil =>
        have mem : t ∈ L.toFinset := e.trans et.symm ▸ Finset.mem_singleton_self _
        exact False.elim (done (List.mem_toFinset.mp mem))
      | @step K a b o m c T ne fresh g tail =>
        obtain ⟨N,hm,hN⟩ := move_covers e ne (e ▸ fresh) g (by omega : credit a b K ≤ cap)
        apply List.any_eq_true.mpr
        exact ⟨(o,N,credit a b K),hm,ih (hN ▸ et.symm ▸ tail) (by omega) (by change c ≤ cap - credit a b K; omega)⟩


def excludes (I : List (BitVec w)) (t : BitVec w) (K : Nat) : Bool :=
  I.sublists.all fun L => !(search t K (K+1-L.toFinset.card) L)

/-- A negative answer for every demanded input subset certifies the unrestricted
signed circuit lower bound with constants and arbitrary sharing. -/
theorem excludes_sound (hw : 0<w) (I : List (BitVec w)) (t : BitVec w) (K : Nat)
    (normI : ∀ a ∈ I, a.getLsbD 0 = false) (normT : t.getLsbD 0 = false)
    (hotT : nonconstant (read t)) (h : excludes I t K = true) : NoAtMost I t K := by
  intro k hk W r out
  obtain ⟨U,sub,m,hm,c,tr,account⟩ := realize hw I t normI normT hotT r out
  let L := I.filter (fun x => decide (x ∈ U))
  have eq : L.toFinset = U := by
    ext x
    simp only [L,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right, fun hx => ⟨List.mem_toFinset.mp (sub hx),hx⟩⟩
  have included : L ∈ I.sublists := List.mem_sublists.mpr (List.filter_sublist ..)
  have failed := List.all_eq_true.mp h L included
  have complete := @search_complete w L t m c (eq ▸ to_tail tr) K (K+1-L.toFinset.card)
    (by omega) (by rw [eq]; omega)
  simp [complete] at failed

#print axioms excludes_sound

end PetersenFrontierSearch
