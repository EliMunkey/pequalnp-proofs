import PetersenMonotoneFrontier
import Mathlib.Data.Finset.Max
import PetersenFrontierSearch
open PetersenSignedBridge PetersenFrontier PetersenPhysicalWords PetersenWordCost PetersenMonotoneFrontier PetersenFrontierSearch
namespace PetersenAntichain
variable {w : Nat}
abbrev B := BitVec w

def correct (t x : BitVec w) := Finset.univ.filter (fun j : Fin w => read x j = read t j)

theorem order (t x y : BitVec w) : Better t x y ↔ correct t x ⊆ correct t y := by
  simp only [correct,Finset.subset_iff,Finset.mem_filter,Finset.mem_univ,true_and,Better]

theorem anti {t a b : BitVec w} (p : Better t a b) (q : Better t b a) : a=b := by
  apply read_inj; funext i
  have f:=p i; have g:=q i
  have bb : ∀ t a b:Bool,(a=t→b=t) → (b=t→a=t) → a=b := by decide
  exact bb _ _ _ f g

def Peak (t : BitVec w) (S : Finset (BitVec w)) (x : BitVec w) := ∀y∈S,Better t x y → x=y

def Anti (t : BitVec w) (S : Finset (BitVec w)) := ∀x∈S, Peak t S x

private theorem choose {t x : BitVec w} {S : Finset (BitVec w)} (mem : x∈S) :
    ∃y∈S, Better t x y ∧ Peak t S y := by
  classical
  let A:=S.filter (Better t x)
  have hx : x∈A := Finset.mem_filter.mpr ⟨mem,PetersenMonotoneFrontier.refl t x⟩
  obtain ⟨y,hy,best⟩:=Finset.exists_max_image A (fun z=>(correct t z).card) ⟨x,hx⟩
  obtain ⟨inS,xy⟩:=Finset.mem_filter.mp hy
  refine ⟨y,inS,xy,?_⟩
  intro z hz yz
  have card:=best z (Finset.mem_filter.mpr ⟨hz,trans xy yz⟩)
  have equal:=Finset.Subset.antisymm_iff.mpr (show correct t y ⊆ correct t z ∧ correct t z ⊆ correct t y from
    ⟨(order ..).mp yz,by rw [Finset.eq_of_subset_of_card_le ((order ..).mp yz) card]⟩)
  exact anti yz ((order ..).mpr equal.ge)

theorem peakOf (t : BitVec w) {S : Finset (BitVec w)} {x} (h : Avail S x) :
    ∃ y, Avail S y ∧ Better t x y ∧ Peak t S y := by
  let A:=insert (0:BitVec w) (insert (~~~0) S)
  have hx : x∈A := by simpa [A,Avail] using h
  obtain ⟨y,hy,imp,maxi⟩:=choose (t:=t) hx
  refine ⟨y,by simpa [A,Avail] using hy,imp,fun z hz=>maxi z ?_⟩
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)

inductive Greedy (t : BitVec w) (I : Finset (BitVec w)) : Nat → Finset (BitVec w) → Prop where
  | start : Greedy t I 0 I
  | add {k S a b o} : Greedy t I k S → a∈S → b∈S → Peak t S a → Peak t S b → a≠b → o∉S →
      (∀v∈S, ¬Better t o v) → CleanGate t I a b o → Greedy t I (k+1) (insert o S)

inductive ATrace (t : BitVec w) (I U : Finset (BitVec w)) : Nat → Nat → Finset (BitVec w) → Prop where
  | start : Anti t U → ATrace t I U 0 0 U
  | step {m c K a b o} : ATrace t I U m c (insert a (insert b K)) →
      a≠b → o∉insert a (insert b K) → (∀v∈insert a (insert b K), ¬Better t o v) → CleanGate t I a b o → Anti t (insert o K) →
      ATrace t I U (m+1) (c+credit a b K) (insert o K)

theorem schedule {I T : Finset (BitVec w)} {t k} (r : Greedy t I k T) (D : Finset (BitVec w))
    (sub : D⊆T) (maxi : ∀x∈D, Peak t T x) : ∃ U⊆I,∃m≤k,∃c,ATrace t I U m c D := by
  have ant : Anti t D := fun x hx y hy=>maxi x hx y (sub hy)
  induction r generalizing D with
  | start => exact ⟨D,sub,0,le_rfl,0,.start ant⟩
  | @add k S a b o _ ha hb ma mb ne fresh exclusive g ih =>
    by_cases used:o∈D
    · let K:=D.erase o
      have Ksub : K ⊆ S := by
        intro x hx; obtain ⟨no,mem⟩:=Finset.mem_erase.mp hx; exact (Finset.mem_insert.mp (sub mem)).resolve_left no
      have old : insert a (insert b K)⊆S := Finset.insert_subset ha (Finset.insert_subset hb Ksub)
      have peaks : ∀x∈insert a (insert b K),Peak t S x := by
        intro x hx; rcases Finset.mem_insert.mp hx with rfl|hw
        · exact ma
        rcases Finset.mem_insert.mp hw with rfl|hk
        · exact mb
        · exact fun z hz=>maxi x (Finset.mem_of_mem_erase hk) z (Finset.mem_insert_of_mem hz)
      obtain ⟨U,ui,m,hm,c,pre⟩:=ih _ old peaks (fun x hx z hz=>peaks x hx z (old hz))
      have eq : insert o K=D := Finset.insert_erase used
      have step:=ATrace.step pre ne (fun h=>fresh (old h)) (fun v h=>exclusive v (old h)) g (eq ▸ ant)
      exact ⟨U,ui,_,by omega,_,eq ▸ step⟩
    · have smaller : D⊆S := by
        intro x hx; rcases Finset.mem_insert.mp (sub hx) with rfl|q
        · exact (used hx).elim
        · exact q
      obtain ⟨U,ui,m,hm,c,pre⟩:=ih _ smaller (fun x hx v hv=>maxi x hx v (Finset.mem_insert_of_mem hv)) ant
      exact ⟨U,ui,m,by omega,c,pre⟩

theorem greedy {raw : List (BitVec w)} {k W} (r : Positive raw k W)
    (t : BitVec w) (I : Finset (BitVec w)) (init : ∀x∈raw, Sim t I x) :
    ∃ m≤k, ∃ S, Greedy t I m S ∧ I⊆S ∧ ∀x∈W, Sim t S x := by
  classical
  induction r with
  | start => exact ⟨0,le_rfl,I,Greedy.start,fun _ h=>h,init⟩
  | @add k W a b op _ ha hb ih =>
    obtain ⟨m,hm,S,pre,sub,cov⟩:=ih
    obtain ⟨u,hu,bu⟩:=cov a ha
    obtain ⟨v,hv,bv⟩:=cov b hb
    obtain ⟨x,hx,ux,mx⟩:=peakOf t hu
    obtain ⟨y,hy,vy,my⟩:=peakOf t hv
    have bx:=trans bu ux
    have byy:=trans bv vy
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
      refine ⟨m+1,by omega,_,Greedy.add pre ax ay mx my ne fresh (fun v hv p=>old ⟨v,Or.inr (Or.inr hv),p⟩) clean,sub.trans inc,?_⟩
      intro v h
      rcases List.mem_cons.mp h with rfl|h
      · exact ⟨o,Or.inr (Or.inr (Finset.mem_insert_self o S)),improve⟩
      · obtain ⟨z,hz,bz⟩:=cov v h
        exact ⟨z,retain inc hz,bz⟩

theorem source {X : Type} (rows : Fin w → X) {init W : List (Func X)} {k} (r : Direct init k W)
    {t : BitVec w} {f : Func X} (output : f∈W) (goal : pack (f ∘ rows)=t)
    (hot : t≠0 ∧ t ≠ ~~~0) (I : Finset (BitVec w))
    (initOK : ∀a∈init, Sim t I (pack (a ∘ rows))) :
    ∃ U ⊆ I, ∃ m≤k, ∃ c, ATrace t I U m c {t} := by
  obtain ⟨j,hj,S,p,_,cov⟩:=greedy (sample rows r) t I (by
    intro x hx; obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hx; exact initOK a ha)
  obtain ⟨u,hu,bu⟩:= cov t (List.mem_map.mpr ⟨f,output,goal⟩)
  have eq := sink bu
  subst u
  have mem : t∈S := hu.resolve_left hot.1 |>.resolve_left hot.2
  obtain ⟨U,sub,m,hm,c,tr⟩:=schedule p {t} (Finset.singleton_subset_iff.mpr mem) (by
    intro x hx; obtain rfl:=Finset.mem_singleton.mp hx; intro y _ good; exact (sink good).symm)
  exact ⟨U,sub,m,by omega,c,tr⟩


/-- Forward-view suffix with target-incomparable live signals before every gate. -/
inductive ATail (t : BitVec w) (I : Finset (BitVec w)) : Finset (BitVec w) → Nat → Nat → Finset (BitVec w) → Prop where
  | nil (W) : Anti t W → ATail t I W 0 0 W
  | step {K a b o m c T} : Anti t (insert a (insert b K)) → a≠b → o∉insert a (insert b K) →
      (∀v∈insert a (insert b K), ¬Better t o v) → CleanGate t I a b o → ATail t I (insert o K) m c T →
      ATail t I (insert a (insert b K)) (m+1) (credit a b K+c) T

theorem ATrace.finalAnti {t : BitVec w} {I U m c S} (p : ATrace t I U m c S) : Anti t S := by
  cases p with
  | start a => exact a
  | step _ _ _ _ _ a => exact a

theorem toATail {t : BitVec w} {I U m c S} (p : ATrace t I U m c S) : ATail t I U m c S := by
  suffices join : ∀ {d s T}, ATail t I S d s T → ATail t I U (m+d) (c+s) T by
    simpa using join (ATail.nil S p.finalAnti)
  induction p with
  | start _ => intro _ _ _ q; simpa using q
  | step pre ne fr ex g _ ih =>
    intro d s T q
    have append := ih (ATail.step pre.finalAnti ne fr ex g q)
    convert append using 1 <;> omega

theorem ATail.toTail {t : BitVec w} {I U m c T} (p : ATail t I U m c T) : Tail (CleanGate t I) U m c T := by
  induction p with
  | nil S _ => exact .nil S
  | step _ ne fr _ g _ ih => exact .step ne fr g ih

theorem ATail.liveAnti {t : BitVec w} {I U m c T} (p : ATail t I U m c T) : Anti t U := by
  cases p with
  | nil _ a => exact a
  | step a _ _ _ _ _ => exact a

#print axioms source
#print axioms toATail
end PetersenAntichain
