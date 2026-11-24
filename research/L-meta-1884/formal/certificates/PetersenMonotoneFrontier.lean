import PetersenPhysicalWords
import PetersenFrontierSearch
open PetersenSignedBridge PetersenFrontier PetersenFrontierSearch PetersenWordCost PetersenPhysicalWords
namespace PetersenMonotoneFrontier
variable {w : Nat}

/-- A replacement preserves every row where the old word already agrees with the goal. -/
def Better (t a b : BitVec w) : Prop := ∀ r : Fin w, read a r = read t r → read b r = read t r

theorem refl (t x : BitVec w) : Better t x x := fun _ => id
theorem trans {t a b c : BitVec w} (h : Better t a b) (j : Better t b c) : Better t a c :=
  fun i p => j i (h i p)
theorem sink {t a : BitVec w} (h : Better t t a) : a=t := read_inj (funext fun i => h i rfl)

theorem move {t a b x y : BitVec w} (op : Bool) (ax : Better t a x) (byy : Better t b y) :
    Better t (gate op a b) (gate op x y) := by
  intro i
  have l := ax i; have r := byy i
  have rules : ∀ m a b x y op : Bool, (a=m→x=m) → (b=m→y=m) →
      (if op then a||b else a&&b)=m → (if op then x||y else x&&y)=m := by decide
  cases op
  · simpa [PetersenWordCost.gate,PetersenWordCost.read] using rules (read t i) _ _ _ _ false l r
  · simpa [PetersenWordCost.gate,PetersenWordCost.read] using rules (read t i) _ _ _ _ true l r

def Avail (S : Finset (BitVec w)) (x : BitVec w) := x=0 ∨ x = ~~~0 ∨ x∈S

def Sim (t : BitVec w) (S : Finset (BitVec w)) (x : BitVec w) := ∃ y, Avail S y ∧ Better t x y

def CleanGate (t : BitVec w) (I : Finset (BitVec w)) (a b o : BitVec w) : Prop :=
  (∃ op, o=gate op a b) ∧ ∀ v, Avail I v → ¬ Better t o v

theorem retain {S V : Finset (BitVec w)} (sub : S⊆V) {y} : Avail S y → Avail V y :=
  fun h => h.imp_right (fun u => u.imp_right (fun e => sub e))

theorem args {S : Finset (BitVec w)} {a b : BitVec w} (op : Bool)
    (ha : Avail S a) (hb : Avail S b) (absent : ¬Avail S (gate op a b)) : a ∈ S ∧ b ∈ S ∧ a≠b := by
  have ra : a∈S := by
    rcases ha with rfl|rfl|mem
    · cases op <;> simp_all [PetersenWordCost.gate,Avail]
    · cases op <;> simp_all [PetersenWordCost.gate,Avail]
    · exact mem
  have rb : b∈S := by
    rcases hb with rfl|rfl|mem
    · cases op <;> simp_all [PetersenWordCost.gate,Avail]
    · cases op <;> simp_all [PetersenWordCost.gate,Avail]
    · exact mem
  refine ⟨ra,rb,?_⟩
  rintro rfl
  cases op <;> simp_all [PetersenWordCost.gate,Avail]

/-- Simultaneously improve every old wire, gate by gate. If any existing primary,
constant, or earlier word is already at least as correct as a proposed gate
output, that gate can be bypassed. Arbitrary DAG sharing is preserved. -/
theorem normalize {raw : List (BitVec w)} {k W} (r : Positive raw k W)
    (t : BitVec w) (I : Finset (BitVec w)) (init : ∀x∈raw, Sim t I x) :
    ∃ m≤k, ∃ S, Prefix (CleanGate t I) I m S ∧ I⊆S ∧ ∀x∈W, Sim t S x := by
  classical
  induction r with
  | start => exact ⟨0,le_rfl,I,Prefix.start,fun _ h=>h,init⟩
  | @add k W a b op _ ha hb ih =>
    obtain ⟨m,hm,S,pre,sub,cov⟩:=ih
    obtain ⟨x,hx,bx⟩:=cov a ha
    obtain ⟨y,hy,byy⟩:=cov b hb
    let o := gate op x y
    have improve : Better t (gate op a b) o := move op bx byy
    by_cases old : Sim t S o
    · obtain ⟨z,hz,bz⟩:=old
      refine ⟨_,by omega,_,pre,sub,?_⟩
      intro v h
      rcases List.mem_cons.mp h with rfl|h
      · exact ⟨z,hz,trans improve bz⟩
      · exact cov v h
    · have absent : ¬Avail S o := fun e => old ⟨o,e,refl t o⟩
      obtain ⟨ax,ay,ne⟩:=args op hx hy absent
      have clean : CleanGate t I x y o := ⟨⟨op,rfl⟩,fun v hv h => old ⟨v,retain sub hv,h⟩⟩
      have fresh : o∉S := fun h => absent (Or.inr (Or.inr h))
      have inc : S⊆insert o S := fun _ h => Finset.mem_insert_of_mem h
      refine ⟨m+1,by omega,_,Prefix.add pre ax ay ne fresh clean,sub.trans inc,?_⟩
      intro v h
      rcases List.mem_cons.mp h with rfl|h
      · exact ⟨o,Or.inr (Or.inr (Finset.mem_insert_self o S)),improve⟩
      · obtain ⟨z,hz,bz⟩:=cov v h
        exact ⟨z,retain inc hz,bz⟩

/-- The whole physical DAG yields an ordinary last-use frontier whose generated
words are undominated by any primary or constant. -/
theorem realize {X : Type} (rows : Fin w → X) {init W : List (Func X)} {k} (r : Direct init k W)
    {t : BitVec w} {f : Func X} (output : f∈W) (goal : pack (f ∘ rows)=t)
    (hot : t≠0 ∧ t ≠ ~~~0) (I : Finset (BitVec w))
    (initOK : ∀a∈init, Sim t I (pack (a ∘ rows))) :
    ∃ U ⊆ I, ∃ m≤k, ∃ c, Trace (CleanGate t I) U m c {t} ∧ m+1=U.card+c := by
  obtain ⟨j,hj,S,p,_,cov⟩:=normalize (sample rows r) t I (by
    intro x hx; obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hx; exact initOK a ha)
  obtain ⟨u,hu,bu⟩:= cov t (List.mem_map.mpr ⟨f,output,goal⟩)
  have eq := sink bu
  subst u
  have mem : t∈S := hu.resolve_left hot.1 |>.resolve_left hot.2
  obtain ⟨U,sub,m,hm,c,tr⟩:=p.schedule {t} (Finset.singleton_subset_iff.mpr mem)
  exact ⟨U,sub,m,by omega,c,tr,tr.sink⟩

#print axioms realize
end PetersenMonotoneFrontier
