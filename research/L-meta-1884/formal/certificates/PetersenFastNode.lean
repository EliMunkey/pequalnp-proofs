import PetersenLayerCheck
open PetersenFrontier PetersenPackedFrontier PetersenFrontierSearch PetersenLayerCheck PetersenWordCost
namespace PetersenFastNode
variable {w : Nat}

def mismatch (t : BitVec w) (L : List (BitVec w)) (i j : Nat) : Bool :=
  decide (i < w) && decide (j < w) && (t.getLsbD i != t.getLsbD j) &&
  L.all fun x => x.getLsbD i == x.getLsbD j

theorem mismatch_sound {t : BitVec w} {L : List (BitVec w)} {i j fuel : Nat}
    (h : mismatch t L i j = true) : Blocked t fuel L := by
  intro m hm c tail
  simp only [mismatch,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne,List.all_eq_true,beq_iff_eq] at h
  obtain ⟨⟨⟨hi,hj⟩,neq⟩,ag⟩ := h
  exact neq (tail_agree tail ⟨i,hi⟩ ⟨j,hj⟩ (fun x hx => ag x (List.mem_toFinset.mp hx)) t
    (Finset.mem_singleton_self _))

def hintOK (t : BitVec w) (nxt : Array (List (BitVec w))) (L : List (BitVec w)) (hint : Nat) : Bool :=
  if j : hint < nxt.size then same L nxt[hint] else
    let q := hint-nxt.size
    mismatch t L (q / w) (q % w)

private theorem hint_sound {t : BitVec w} {nxt : Array (List (BitVec w))} {L : List (BitVec w)} {hint k}
    (h : hintOK t nxt L hint = true) (valid : ∀ V ∈ nxt.toList, Blocked t k V) : Blocked t k L := by
  unfold hintOK at h
  split at h
  · rename_i j
    have eq := same_spec h
    intro m hm c tail
    exact valid nxt[hint] (by simp) m hm c (eq ▸ tail)
  · exact mismatch_sound h

def walk (t : BitVec w) (nxt : Array (List (BitVec w))) :
    List (BitVec w × List (BitVec w) × Nat) → List Nat → Bool
  | [], [] => true
  | (_,v,_)::vs, h::hs => hintOK t nxt v h && walk t nxt vs hs
  | _,_ => false

theorem covers {t : BitVec w} {nxt : Array (List (BitVec w))}
    {vs : List (BitVec w × List (BitVec w) × Nat)} {hs} (h : walk t nxt vs hs = true)
    {k} (ok : ∀ V∈nxt.toList, Blocked t k V) {a : BitVec w × List (BitVec w) × Nat} (ha : a∈vs) :
    Blocked t k a.2.1 := by
  induction vs generalizing hs with
  | nil => simp at ha
  | cons v vs ih =>
    rcases v with ⟨o,L,c⟩
    cases hs with
    | nil => simp [walk] at h
    | cons hint rest =>
      obtain ⟨hh,hr⟩ := Bool.and_eq_true_iff.mp h
      rcases List.mem_cons.mp ha with rfl|mem
      · exact hint_sound hh ok
      · exact ih hr mem

def test (t : BitVec w) (fuel : Nat) (L : List (BitVec w)) (nxt : Array (List (BitVec w)))
    (hints : List Nat) : Bool :=
  !L.contains t && walk t nxt (moves L (fuel+1-L.toFinset.card)) hints

theorem node {t : BitVec w} {d : Nat} {L nxt hints}
    (testOK : test t (d+1) L nxt hints = true) (closed : ∀ V∈nxt.toList, Blocked t d V) :
    Blocked t (d+1) L := by
  obtain ⟨miss,pass⟩ := Bool.and_eq_true_iff.mp testOK
  intro m hm c tail
  have total := tail_count tail
  simp only [Finset.card_singleton] at total
  generalize eq : L.toFinset = S at tail
  generalize dest : ({t} : Finset _) = T at tail
  cases tail with
  | nil =>
    have mem : t ∈ L.toFinset := (eq.trans dest.symm) ▸ Finset.mem_singleton_self _
    simp [List.mem_toFinset.mp mem] at miss
  | @step K a b o m c T ne fresh g tail =>
    obtain ⟨V,mv,v⟩ := move_covers eq ne (eq ▸ fresh) g (by omega : credit a b K ≤ d+1+1-L.toFinset.card)
    exact covers pass closed mv m (by omega) c (v ▸ dest.symm ▸ tail)

end PetersenFastNode
