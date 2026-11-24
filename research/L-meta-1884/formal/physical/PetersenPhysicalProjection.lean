import PetersenPhysicalSearch
import PetersenPackedPin

open PetersenPhysicalWords PetersenPhysicalSearch PetersenPackedPin PetersenFrontierSearch PetersenWordCost
namespace PetersenPhysicalProjection

variable {w u : Nat}

private theorem project_gate (r : Fin u → Fin w) (op : Bool) (a b : BitVec w) :
    project r (gate op a b) = gate op (project r a) (project r b) := by
  apply read_inj
  simp only [project, read_pack]
  funext i
  have ha := congrFun (read_pack (PetersenWordCost.read a ∘ r)) i
  have hb := congrFun (read_pack (PetersenWordCost.read b ∘ r)) i
  cases op <;> simp [gate,PetersenWordCost.read,Function.comp_def] at * <;> simp [ha,hb]

private theorem project_neg (r : Fin u → Fin w) (a : BitVec w) :
    project r (~~~a) = ~~~project r a := by
  apply read_inj
  funext i
  have eq := congrFun (read_pack (PetersenWordCost.read a ∘ r)) i
  have ne := congrFun (read_pack (PetersenWordCost.read (~~~a) ∘ r)) i
  change (project r (~~~a)).getLsbD i.val = _ at ne
  change (project r a).getLsbD i.val = _ at eq
  change (project r (~~~a)).getLsbD i.val = (~~~project r a).getLsbD i.val
  rw [ne,BitVec.getLsbD_not,eq]
  simp [PetersenWordCost.read,i.isLt,(r i).isLt]

def pinned (r : Fin u → Fin w) (a : BitVec w) : Prop :=
  project r a = 0 ∨ project r a = ~~~0

instance (r : Fin u → Fin w) (a : BitVec w) : Decidable (pinned r a) :=
  inferInstanceAs (Decidable (_ ∨ _))

def covers (r : Fin u → Fin w) (p : BitVec w) (V : List (BitVec u)) (a : BitVec w) : Prop :=
  ∀ x ∈ literals p a, project r x ∈ V

private theorem lit_const (r : Fin u → Fin w) (p a x : BitVec w)
    (c : pinned r a) (h : x ∈ literals p a) : pinned r x := by
  by_cases e : a=p
  · simp [literals,e] at h
    rcases h with rfl|rfl
    · exact e ▸ c
    · subst a
      unfold pinned at *
      rw [project_neg]
      rcases c with q|q <;> simp [q]
  · simp [literals,e] at h
    exact h ▸ c

private theorem fresh_gate {p a b o : BitVec w} (g : WordGate p a b o) (fresh : o ≠ p) :
    ∃ x ∈ literals p a, ∃ y ∈ literals p b, ∃ op, o = gate op x y := by
  obtain ⟨⟨x,y⟩,hx,ho⟩ := List.mem_flatMap.mp g
  obtain ⟨ax,byy⟩ := List.mem_product.mp hx
  refine ⟨x,ax,y,byy,?_⟩
  have idKey (v : BitVec w) (hn : key p v ≠ p) : key p v = v := by
    unfold key at *; split at hn <;> simp_all
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl
  · exact ⟨false,idKey _ fresh⟩
  · exact ⟨true,idKey _ fresh⟩

private theorem constant_output (r : Fin u → Fin w) {p a b o : BitVec w} (h : WordGate p a b o)
    (fresh : o ≠ p) (ca : pinned r a) (cb : pinned r b) : pinned r o := by
  obtain ⟨x,hx,y,hy,op,rfl⟩ := fresh_gate h fresh
  have ax := lit_const r p a x ca hx
  have byy := lit_const r p b y cb hy
  unfold pinned at *
  rw [project_gate]
  rcases ax with ex|ex <;> rcases byy with ey|ey <;> cases op <;> simp [gate,ex,ey]

private theorem folded {V : List (BitVec u)} (cs : 0∈V ∧ ~~~0∈V)
    {a b : BitVec u} (ha : a∈V) (hb : b∈V) (op : Bool)
    (h : (a=0 ∨ a= ~~~0) ∨ (b=0 ∨ b= ~~~0)) : gate op a b ∈ V := by
  rcases h with (rfl|rfl)|(rfl|rfl) <;> cases op <;> simp_all [gate]

private theorem gate_sim (r : Fin u → Fin w) {p a b o : BitVec w} (g : WordGate p a b o)
    (fresh : o ≠ p) {I V : List (BitVec u)} {j} (pre : Positive I j V)
    (cs : 0∈V ∧ ~~~0∈V) (ha : covers r p V a) (hb : covers r p V b) :
    ∃ S, Positive I (j+PetersenTracePin.debit (pinned r) a b) S ∧ covers r p S o ∧ V ⊆ S := by
  obtain ⟨x,hx,y,hy,op,eq⟩ := fresh_gate g fresh
  have ax := ha x hx
  have byy := hb y hy
  have e : project r o = gate op (project r x) (project r y) := eq ▸ project_gate r op x y
  have sole {S : List (BitVec u)} (v : project r o ∈ S) : covers r p S o := by
    intro z hz
    simp [literals,fresh] at hz
    exact hz ▸ v
  by_cases cheap : pinned r a ∨ pinned r b
  · simp only [PetersenTracePin.debit,ite_eq_left cheap,Nat.add_zero]
    refine ⟨V,pre,sole (e ▸ folded cs ax byy op ?_),fun _ h => h⟩
    exact cheap.imp (fun t => lit_const r p a x t hx) (fun t => lit_const r p b y t hy)
  · simp only [PetersenTracePin.debit,ite_eq_right cheap]
    refine ⟨_,Positive.add op pre ax byy,sole (e ▸ List.mem_cons_self ..),?_⟩
    exact fun _ h => List.mem_cons_of_mem _ h

theorem restrict_tail (r : Fin u → Fin w) {B : Finset (BitVec w)} {p : BitVec w} (present : p∈B)
    {A T m c} (tail : Tail (Allowed B p) A m c T) {I V : List (BitVec u)} {q}
    (pre : Positive I q V) (cs : 0∈V ∧ ~~~0∈V) (all : ∀ a∈A, covers r p V a) :
    ∃ j S, Positive I j S ∧ (∀ a∈T, covers r p S a) ∧
      j + (A.filter (pinned r)).card ≤ q + m + (T.filter (pinned r)).card := by
  induction tail generalizing q V with
  | nil => exact ⟨q,V,pre,all,by omega⟩
  | @step K a b o m c T ne fresh h _ ih =>
    have np : o ≠ p := fun e => h.1 (e ▸ present)
    obtain ⟨S,pr,cv,sub⟩ := gate_sim r h.2 np pre cs (all a (Finset.mem_insert_self ..))
      (all b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..)))
    have step := PetersenTracePin.step_budget (pinned r) ne fresh (constant_output r h.2 np)
    obtain ⟨j,Z,rs,done,bound⟩ := ih pr ⟨sub cs.1,sub cs.2⟩ (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl|hk
      · exact cv
      · exact fun z hz => sub (all x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hk)) z hz))
    exact ⟨j,Z,rs,done,by omega⟩

def NoPhysical (I : List (BitVec u)) (t : BitVec u) (K : Nat) : Prop :=
  ∀ j ≤ K, ∀ S, Positive I j S → t ∉ S

/-- Projecting an arbitrary live frontier to a certified smaller positive instance rules out
    every suffix whose budget is exhausted by the projected circuit and pinned live wires. -/
theorem blocks {B : List (BitVec w)} {p : BitVec w} (present : p ∈ B.toFinset)
    (r : Fin u → Fin w) {t : BitVec w} {I V : List (BitVec u)} {q K fuel}
    (small : NoPhysical I (project r t) K) (hot : ¬pinned r t)
    (pre : Positive I q V) (cs : 0∈V ∧ ~~~0∈V) (L : List (BitVec w))
    (cover : ∀ a∈L, covers r p V a)
    (fail : q + fuel < K+1 + (L.toFinset.filter (pinned r)).card) :
    Blocked B p t fuel L := by
  intro m hm c tail
  obtain ⟨j,S,pr,out,le⟩ := restrict_tail r present tail pre cs
    (fun a ha => cover a (List.mem_toFinset.mp ha))
  have old : t∈literals p t := by by_cases e : t=p <;> simp [literals,e]
  have mem := out t (Finset.mem_singleton_self _) t old
  have emp : (({t} : Finset _).filter (pinned r)).card = 0 := by simp [hot]
  rw [emp] at le
  exact small j (by omega) S pr mem

#print axioms restrict_tail
#print axioms blocks
end PetersenPhysicalProjection
