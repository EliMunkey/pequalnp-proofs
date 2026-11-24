import PetersenLayerCheck
import PetersenPackedPin

open PetersenFrontier PetersenFrontierSearch PetersenPackedFrontier PetersenWordCost
open PetersenLayerCheck PetersenPackedPin
namespace PetersenSymmetry
variable {w : Nat}

/-- A map on words need only be injective and carry every legal gate to a legal gate. -/
structure Action (w : Nat) where
  word : BitVec w ↪ BitVec w
  gate : ∀ {a b o}, signedWordGate a b o → signedWordGate (word a) (word b) (word o)

theorem map_tail {G : BitVec w → BitVec w → BitVec w → Prop}
    (e : BitVec w ↪ BitVec w) (gate : ∀ {a b o}, G a b o → G (e a) (e b) (e o))
    {I T m c} (r : Tail G I m c T) : Tail G (I.map e) m c (T.map e) := by
  induction r with
  | nil => exact .nil _
  | @step K a b o m c T ab fresh hg _ ih =>
    simp only [Finset.map_insert] at ih ⊢
    have no : e o ∉ insert (e a) (insert (e b) (K.map e)) := by
      simpa only [←Finset.map_insert,Finset.mem_map'] using fresh
    have cr : credit (e a) (e b) (K.map e) = credit a b K := by simp [credit]
    rw [← cr]
    exact .step (fun x => ab (e.injective x)) no (gate hg) ih

/-- The old and representative live lists may be ordered differently. -/
theorem via (sym : Action w) {t : BitVec w} (fixT : sym.word t = t) {k}
    {rep L : List (BitVec w)} (align : same (L.map sym.word) rep = true)
    (h : Blocked t k rep) : Blocked t k L := by
  intro m le c r
  have mapped := map_tail sym.word (@sym.gate) r
  have eq : L.toFinset.map sym.word = rep.toFinset := by
    rw [←same_spec align]
    ext v
    simp [List.mem_map,Finset.mem_map]
  rw [eq,Finset.map_singleton,fixT] at mapped
  exact h m le c mapped

/-- Read semantics allows bit-permutation implementations to be substituted for the
literal row loop. Fixing the zero row commutes with the signed representative choice. -/
def ofRows (hw : 0 < w) (p : Fin w → Fin w) (onto : Function.Surjective p)
    (p0 : p ⟨0,hw⟩ = ⟨0,hw⟩) (word : BitVec w → BitVec w)
    (reads : ∀ (a : BitVec w) (i : Fin w), read (word a) i = read a (p i)) : Action w := by
  let e : BitVec w ↪ BitVec w := ⟨word,by
    intro a b eq; apply read_inj; funext j; obtain ⟨i,rfl⟩ := onto j
    rw [←reads,←reads,eq]⟩
  have rn (a : BitVec w) (i : Fin w) : PetersenWordCost.read (~~~a) i = !(PetersenWordCost.read a i) := by
    simp [PetersenWordCost.read,i.isLt]
  have ra (a b : BitVec w) (i : Fin w) : PetersenWordCost.read (a &&& b) i =
      (PetersenWordCost.read a i && PetersenWordCost.read b i) := by simp [PetersenWordCost.read]
  have ro (a b : BitVec w) (i : Fin w) : PetersenWordCost.read (a ||| b) i =
      (PetersenWordCost.read a i || PetersenWordCost.read b i) := by simp [PetersenWordCost.read]
  have neg (a : BitVec w) : word (~~~a) = ~~~word a := by
    apply read_inj; funext i; rw [reads,rn,rn,reads]
  have band (a b : BitVec w) : word (a &&& b) = word a &&& word b := by
    apply read_inj; funext i; rw [reads,ra,ra,reads,reads]
  have bor (a b : BitVec w) : word (a ||| b) = word a ||| word b := by
    apply read_inj; funext i; rw [reads,ro,ro,reads,reads]
  have normed (a : BitVec w) : word (norm a) = norm (word a) := by
    have z := reads a ⟨0,hw⟩
    rw [p0] at z
    change (word a).getLsbD 0 = a.getLsbD 0 at z
    cases h : a.getLsbD 0 <;> simp [norm,z,h,neg]
  refine ⟨e,?_⟩
  intro a b o g
  obtain ⟨⟨x,y⟩,xy,ho⟩ := List.mem_flatMap.mp g
  obtain ⟨hx,hy⟩ := List.mem_product.mp xy
  have sign {a x : BitVec w} (s : x ∈ [a,~~~a]) : word x ∈ [e a,~~~e a] := by
    change word x ∈ [word a,~~~(word a)]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at s
    rcases s with rfl|rfl <;> simp [neg]
  apply List.mem_flatMap.mpr
  refine ⟨(word x,word y),List.mem_product.mpr ⟨sign hx,sign hy⟩,?_⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  change word o ∈ [norm (word x &&& word y),norm (word x ||| word y)]
  rcases ho with rfl|rfl <;> simp [normed,band,bor]

#print axioms via
#print axioms ofRows
end PetersenSymmetry
