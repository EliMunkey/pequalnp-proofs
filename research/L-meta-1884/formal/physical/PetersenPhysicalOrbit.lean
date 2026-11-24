import PetersenPhysicalRowGroup
import PetersenPhysicalSearch
open PetersenSignedBridge PetersenFrontier PetersenFrontierSearch PetersenPhysicalWords PetersenPhysicalCut
open PetersenFrontierSymmetry PetersenPhysicalRowGroup
namespace PetersenPhysicalOrbit
abbrev B := BitVec 38
abbrev sources : List B := List.ofFn word
abbrev p : B := word 0
abbrev G := PetersenPhysicalSearch.Allowed sources.toFinset p
abbrev Blocked := PetersenPhysicalSearch.Blocked sources p label

theorem swap {a b o : B} (gate : WordGate p a b o) : WordGate p b a o := by
  obtain ⟨⟨x,y⟩,pair,h⟩ := List.mem_flatMap.mp gate
  obtain ⟨hx,hy⟩ := List.mem_product.mp pair
  exact List.mem_flatMap.mpr ⟨(y,x),List.mem_product.mpr ⟨hy,hx⟩,by
    simpa only [BitVec.and_comm y x,BitVec.or_comm y x] using h⟩

theorem mapKey (s : Aut) (v : B) : act s.row (key p v) = key p (act s.row v) := by
  have n : act s.row (~~~p) = ~~~p := by rw [act_not,pivot_act]
  have eq : act s.row v = ~~~p ↔ v = ~~~p := by
    calc
      _ ↔ act s.row v = act s.row (~~~p) := by rw [n]
      _ ↔ _ := (act_injective s.row).eq_iff
  by_cases h : v = ~~~p
  · rw [key,ite_eq_left h,key,ite_eq_left (eq.mpr h),pivot_act]
  · rw [key,ite_eq_right h,key,ite_eq_right (fun e => h (eq.mp e))]

theorem mapGate (s : Aut) {a b o : B} (gate : WordGate p a b o) :
    WordGate p (act s.row a) (act s.row b) (act s.row o) := by
  obtain ⟨⟨x,y⟩,pair,h⟩ := List.mem_flatMap.mp gate
  obtain ⟨hx,hy⟩ := List.mem_product.mp pair
  have lit {v u : B} (h : u∈literals p v) : act s.row u ∈ literals p (act s.row v) := by
    by_cases e : v=p
    · subst v; simp only [literals,ite_true,pivot_act,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      rcases h with rfl|rfl
      · exact Or.inl (pivot_act s)
      · exact Or.inr ((act_not ..).trans (congrArg (~~~·) (pivot_act s)))
    · have n : act s.row v ≠ p := fun h => e (act_injective s.row (h.trans (pivot_act s).symm))
      simpa [literals,e,n] using congrArg (act s.row) (show u=v by simpa [literals,e] using h)
  refine List.mem_flatMap.mpr ⟨(act s.row x,act s.row y),List.mem_product.mpr ⟨lit hx,lit hy⟩,?_⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
  rcases h with rfl|rfl
  · exact Or.inl ((mapKey s _).trans (congrArg (key p) (act_and s.row x y)))
  · exact Or.inr ((mapKey s _).trans (congrArg (key p) (act_or s.row x y)))

theorem mapInputs (s : Aut) : sources.toFinset.map (rowEmb s.row) = sources.toFinset := by
  ext z
  simp only [Finset.mem_map,List.mem_toFinset,List.mem_ofFn]
  constructor
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩; exact ⟨s.vertex i,(primary_act s i).symm⟩
  · rintro ⟨i,rfl⟩
    refine ⟨word (s.vertex.symm i),⟨_,rfl⟩,?_⟩
    change act s.row (word (s.vertex.symm i)) = word i
    rw [primary_act,Equiv.apply_symm_apply]

theorem mapAllowed (s : Aut) {a b o : B} (h : G a b o) : G (act s.row a) (act s.row b) (act s.row o) := by
  refine ⟨?_,mapGate s h.2⟩
  intro mem; apply h.1
  have inMap : rowEmb s.row o ∈ sources.toFinset.map (rowEmb s.row) := by rw [mapInputs]; exact mem
  simpa using inMap

def negatives : List (Fin 38) := (List.finRange 38).filter (fun j => !label.getLsbD j.val)
def checkPair (r : V × V) : Bool :=
  let a := word r.1
  let b := word r.2
  (choices p a b).all fun o => [false,true].all fun ka => [false,true].all fun kb =>
    (ka && kb) || !fits p label negatives (o :: kept sources a b ka kb)

def outputs : List B := reps.flatMap fun (a,b) => choices p (word a) (word b)

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem firstCensus : reps.all checkPair = true ∧ outputs.length=20 ∧ outputs.Nodup ∧
    label ∉ sources.toFinset ∧ p ∈ sources.toFinset := by decide +kernel

/-- Every feasible representative first gate must retain both of its operands. -/
theorem mustKeep {i j : V} (representative : (i,j)∈reps) {K : Finset B} {o m c}
    (old : sources.toFinset = insert (word i) (insert (word j) K))
    (g : WordGate p (word i) (word j) o) (tail : Tail G (insert o K) m c {label}) :
    K=sources.toFinset := by
  let a := word i
  let b := word j
  let ka := decide (a∈K)
  let kb := decide (b∈K)
  have bits (v : Bool) : v∈[false,true] := by cases v <;> simp
  have slab := List.all_eq_true.mp firstCensus.1 (i,j) representative
  have check := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp slab o g) ka (bits ka)) kb (bits kb)
  let L := o :: kept sources a b ka kb
  have state : L.toFinset = insert o K := by
    simp only [L,List.toFinset_cons]; rw [kept_eq old]
  have feasible := fits_tail firstCensus.2.2.2.2 L (state ▸ tail) negatives
  change (ka && kb || !fits p label negatives L) = true at check
  have both := (Bool.or_eq_true_iff.mp check).resolve_right (by simp [feasible])
  obtain ⟨aa,bb⟩ := Bool.and_eq_true_iff.mp both
  have ha : a∈K := of_decide_eq_true aa
  have hb : b∈K := of_decide_eq_true bb
  change sources.toFinset=insert a (insert b K) at old
  rw [Finset.insert_eq_of_mem hb,Finset.insert_eq_of_mem ha] at old
  exact old.symm

/-- These twenty explicit kernels cover all 45 physical source pairs, gate choices,
complement choices at x₀, and last-use patterns whenever the target is reached. -/
theorem twenty (fuel : Nat) (suffix : ∀ o∈outputs, Blocked fuel (o::sources)) : Blocked (fuel+1) sources := by
  intro m hm c run
  generalize old : sources.toFinset = I at run
  generalize stop : ({label} : Finset B) = F at run
  cases run with
  | nil => exact firstCensus.2.2.2.1 ((old.trans stop.symm) ▸ Finset.mem_singleton_self _)
  | @step K a b o m c T ne _ g tail =>
    have am : a∈sources.toFinset := old ▸ Finset.mem_insert_self ..
    have bm : b∈sources.toFinset := old ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    obtain ⟨i,ae⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp am)
    obtain ⟨j,be⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp bm)
    subst a; subst b
    have distinct : i≠j := by rintro rfl; exact ne rfl
    let s := pick i j
    obtain ⟨inReps,orient⟩ := witness i j distinct
    let M := K.map (rowEmb s.row)
    let h := act s.row o
    have tail0 : Tail G (insert o K) m c {label} := by
      change Tail (PetersenPhysicalSearch.Allowed sources.toFinset p) _ _ _ _
      rw [old,stop]
      exact tail
    have moved := tail_map (rowEmb s.row) (fun _ _ _ z => mapAllowed s z) tail0
    rw [Finset.map_insert,Finset.map_singleton] at moved
    have lab : rowEmb s.row label=label := target_act s
    rw [lab] at moved
    have movedOld : sources.toFinset = insert (word (s.vertex i)) (insert (word (s.vertex j)) M) := by
      calc
        _ = sources.toFinset.map (rowEmb s.row) := (mapInputs s).symm
        _ = insert (act s.row (word i)) (insert (act s.row (word j)) M) := by
          rw [old,Finset.map_insert,Finset.map_insert]; rfl
        _ = _ := by rw [primary_act,primary_act]
    have mg : WordGate p (word (s.vertex i)) (word (s.vertex j)) h := by
      have v := mapGate s g.2
      rwa [primary_act,primary_act] at v
    have align : sources.toFinset = insert (word (first i j)) (insert (word (second i j)) M) ∧
        WordGate p (word (first i j)) (word (second i j)) h := by
      rcases orient with ⟨u,v⟩|⟨u,v⟩
      · exact ⟨by simpa only [s,u,v] using movedOld,by simpa only [s,u,v] using mg⟩
      · exact ⟨by simpa only [s,u,v,Finset.insert_comm (word (second i j))] using movedOld,
          by simpa only [s,u,v] using swap mg⟩
    have keep := mustKeep inReps align.1 align.2 moved
    have mem : h ∈ outputs := List.mem_flatMap.mpr ⟨(first i j,second i j),inReps,align.2⟩
    apply suffix h mem m (by omega) c
    rw [List.toFinset_cons]
    change Tail G (insert h M) m c {label} at moved
    rw [keep] at moved
    exact moved

/-- Interface to the posted physical circuit model. At 18 gates, the only
remaining obligations are the twenty explicit 17-gate suffix root states. -/
theorem no_physical {k W} (suffix : ∀ o∈outputs, Blocked k (o::sources))
    (src : PetersenSignedBridge.Direct rails (k+1) W)
    (out : PetersenTarget ∈ W) : False := by
  obtain ⟨m,hm,c,run,_⟩ := PetersenPhysicalDemand.all_ten src out
  rw [initial_eq,pivot_eq,target_eq] at run
  exact twenty k suffix m hm c (to_tail run)

#print axioms no_physical
#print axioms firstCensus
#print axioms twenty
end PetersenPhysicalOrbit
