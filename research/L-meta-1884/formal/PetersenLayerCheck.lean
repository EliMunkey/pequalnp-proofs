import PetersenFrontierSearch

open PetersenSignedBridge PetersenWordCost PetersenFrontier PetersenPackedFrontier PetersenFrontierSearch
namespace PetersenLayerCheck
variable {w : Nat}

theorem tail_count {I T : Finset (BitVec w)} {m c}
    (t : Tail signedWordGate I m c T) : I.card+c=T.card+m := by
  induction t with
  | nil => simp
  | @step K a b o m c T hab fresh g t ih =>
    have ho : o ∉ K := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    by_cases ha : a∈K <;> by_cases hb : b∈K <;>
      simp [ha,hb,ho,hab,credit,Finset.card_insert_of_notMem] at * <;> omega

def same (L V : List (BitVec w)) : Bool :=
  L.all V.contains && V.all L.contains

theorem same_spec {L V : List (BitVec w)} (h : same L V = true) : L.toFinset=V.toFinset := by
  obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp h
  ext x; simp only [List.mem_toFinset]
  exact ⟨fun hx => by simpa using List.all_eq_true.mp left x hx,
    fun hx => by simpa using List.all_eq_true.mp right x hx⟩

def nodeOK (t : BitVec w) (fuel : Nat) (nextLayer : List (List (BitVec w)))
    (L : List (BitVec w)) : Bool :=
  !L.contains t && (moves L (fuel+1-L.toFinset.card)).all fun (_,V,_) =>
    !consistent t V (~~~0) || nextLayer.any (same V)

def Blocked (t : BitVec w) (fuel : Nat) (L : List (BitVec w)) : Prop :=
  ∀ m ≤ fuel, ∀ c, ¬ Tail signedWordGate L.toFinset m c {t}

theorem node_sound {t : BitVec w} {fuel : Nat} {nxt : List (List (BitVec w))} {L}
    (h : nodeOK t (fuel+1) nxt L = true) (closed : ∀ R ∈ nxt, Blocked t fuel R) :
    Blocked t (fuel+1) L := by
  intro m hm c tail
  obtain ⟨miss,pass⟩ := Bool.and_eq_true_iff.mp h
  have total := tail_count tail
  simp only [Finset.card_singleton] at total
  generalize eq : L.toFinset = S at tail
  generalize endEq : ({t} : Finset (BitVec w)) = T at tail
  cases tail with
  | nil =>
    have mem : t ∈ L.toFinset := (eq.trans endEq.symm) ▸ Finset.mem_singleton_self _
    simpa [List.mem_toFinset.mp mem] using miss
  | @step K a b o m c T ne fresh g r =>
    obtain ⟨V,mv,v⟩ := move_covers eq ne (eq ▸ fresh) g (by omega : credit a b K ≤ fuel+1+1-L.toFinset.card)
    have test := List.all_eq_true.mp pass _ mv
    have rt : Tail signedWordGate V.toFinset m c {t} := v ▸ endEq.symm ▸ r
    have ok : consistent t V (~~~0) = true := by
      apply consistent_complete
      intro i j _ _ h
      exact tail_agree rt i j (fun x hx => h _ (List.mem_toFinset.mp hx)) _ (Finset.mem_singleton_self _)
    change (!consistent t V (~~~0) || nxt.any (same V)) = true at test
    simp only [ok,Bool.not_true,Bool.false_or,List.any_eq_true] at test
    obtain ⟨R,hR,matchR⟩ := test
    exact closed _ hR _ (by omega) _ (same_spec matchR ▸ rt)

def rootOK (t : BitVec w) (I : List (BitVec w)) : Bool :=
  I.sublists.all fun L => !consistent t L (~~~0) || same L I

theorem root_sound {t : BitVec w} {I : List (BitVec w)} {K}
    (hw : 0<w) (normI : ∀ a ∈ I, a.getLsbD 0 = false) (normT : t.getLsbD 0 = false)
    (hotT : nonconstant (read t)) (needs : rootOK t I = true) (closed : Blocked t K I) :
    NoAtMost I t K := by
  intro k hk W r out
  obtain ⟨U,sub,m,hm,c,tr,_⟩ := realize hw I t normI normT hotT r out
  let L := I.filter (fun x => decide (x ∈ U))
  have eq : L.toFinset = U := by
    ext x
    simp only [L,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right, fun hx => ⟨List.mem_toFinset.mp (sub hx),hx⟩⟩
  have included : L ∈ I.sublists := List.mem_sublists.mpr (List.filter_sublist ..)
  have good := List.all_eq_true.mp needs L included
  have rt : Tail signedWordGate L.toFinset m c {t} := eq ▸ to_tail tr
  have det : consistent t L (~~~0) = true := by
    apply consistent_complete
    intro i j _ _ h
    exact tail_agree rt i j (fun x hx => h x (List.mem_toFinset.mp hx)) _ (Finset.mem_singleton_self _)
  change (!consistent t L (~~~0) || same L I) = true at good
  simp only [det,Bool.not_true,Bool.false_or] at good
  exact closed m (by omega) c (same_spec good ▸ rt)

#print axioms root_sound
end PetersenLayerCheck
