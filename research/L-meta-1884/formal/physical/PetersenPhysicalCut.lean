import PetersenPhysicalWords
import PetersenFrontierSearch

open PetersenFrontier PetersenFrontierSearch PetersenWordCost PetersenPhysicalWords
namespace PetersenPhysicalCut
variable {w : Nat}

def before (pivot a : BitVec w) (i j : Fin w) : Prop :=
  (PetersenWordCost.read a i = true → PetersenWordCost.read a j = true) ∧
  (a = pivot → PetersenWordCost.read a j = true → PetersenWordCost.read a i = true)

private theorem raw_before (p a v : BitVec w) {i j : Fin w}
    (h : before p a i j) (avail : v ∈ literals p a) :
    PetersenWordCost.read v i = true → PetersenWordCost.read v j = true := by
  by_cases same : a=p
  · simp [literals,same] at avail
    rcases avail with rfl|rfl
    · exact same ▸ h.1
    · subst a
      have inv := h.2 rfl
      simp only [PetersenWordCost.read,BitVec.getLsbD_not,i.isLt,j.isLt,decide_true,Bool.true_and] at *
      cases hi : p.getLsbD i.val <;> cases hj : p.getLsbD j.val <;> simp_all
  · simp [literals,same] at avail
    exact avail ▸ h.1

private theorem monotone_word {p a b o : BitVec w} (g : WordGate p a b o) (fresh : o ≠ p)
    {i j : Fin w} (ha : before p a i j) (hb : before p b i j) : before p o i j := by
  obtain ⟨⟨x,y⟩,hx,ho⟩ := List.mem_flatMap.mp g
  obtain ⟨ax,byy⟩ := List.mem_product.mp hx
  have va := raw_before p a x ha ax
  have vb := raw_before p b y hb byy
  have idKey (v : BitVec w) (hn : key p v ≠ p) : key p v = v := by
    unfold key at *; split at hn <;> simp_all
  refine ⟨?_,fun e => (fresh e).elim⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl <;> rw [idKey _ fresh] <;>
    simp only [PetersenWordCost.read,BitVec.getLsbD_and,BitVec.getLsbD_or,Bool.and_eq_true,Bool.or_eq_true] at * <;> tauto

theorem tail_before {p : BitVec w} {I : Finset (BitVec w)} (hp : p ∈ I)
    {start stop m c} (tail : Tail (fun a b o => o ∉ I ∧ WordGate p a b o) start m c stop)
    (i j : Fin w) (all : ∀ a ∈ start, before p a i j) : ∀ a ∈ stop, before p a i j := by
  induction tail with
  | nil => exact all
  | @step K a b o m c T _ _ g _ ih =>
    apply ih
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl|keep
    · exact monotone_word g.2 (fun eq => g.1 (eq ▸ hp))
        (all a (Finset.mem_insert_self ..)) (all b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..)))
    · exact all f (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem keep))

def mask (p a : BitVec w) (j : Fin w) : BitVec w :=
  if a.getLsbD j.val then (if a == p then a else ~~~0) else ~~~a

theorem mask_spec (p a : BitVec w) (i j : Fin w) :
    (mask p a j).getLsbD i.val = true ↔ before p a i j := by
  by_cases e : a=p <;> cases hi : a.getLsbD i.val <;> cases hj : a.getLsbD j.val <;>
    simp_all [mask,before,PetersenWordCost.read,i.isLt]

def compatible (p : BitVec w) (L : List (BitVec w)) (j : Fin w) (T : BitVec w) : BitVec w :=
  L.foldl (fun s a => s &&& mask p a j) T

theorem compatible_spec (p : BitVec w) (L : List (BitVec w)) (i j : Fin w) (T : BitVec w) :
    (compatible p L j T).getLsbD i.val = true ↔
      T.getLsbD i.val = true ∧ ∀ a ∈ L, before p a i j := by
  induction L generalizing T with
  | nil => simp [compatible]
  | cons a l ih =>
    change (compatible p l j (T &&& mask p a j)).getLsbD i.val = true ↔ _
    rw [ih,BitVec.getLsbD_and,Bool.and_eq_true,mask_spec]
    simp only [List.mem_cons,forall_eq_or_imp]
    tauto

def fits (p t : BitVec w) (testRows : List (Fin w)) (L : List (BitVec w)) : Bool :=
  testRows.all fun j => t.getLsbD j.val || compatible p L j t == 0

theorem fits_tail {p t : BitVec w} {I : Finset (BitVec w)} (hp : p ∈ I) (L : List (BitVec w))
    {m c} (tail : Tail (fun a b o => o ∉ I ∧ WordGate p a b o) L.toFinset m c {t})
    (testRows : List (Fin w)) : fits p t testRows L = true := by
  apply List.all_eq_true.mpr
  intro j _
  apply Bool.or_eq_true_iff.mpr
  cases hj : t.getLsbD j.val with
  | true => exact Or.inl rfl
  | false =>
    right; apply beq_iff_eq.mpr; by_contra nz
    obtain ⟨i,one⟩ := nonzero_witness nz
    obtain ⟨target,all⟩ := (compatible_spec p L i j t).mp one
    have ord := tail_before hp tail i j (fun a ha => all a (List.mem_toFinset.mp ha)) t (Finset.mem_singleton_self _)
    exact Bool.false_ne_true (hj.symm.trans (ord.1 target))

end PetersenPhysicalCut
