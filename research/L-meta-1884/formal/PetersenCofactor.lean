import PetersenPhysicalBoundary

open PetersenSignedBridge

namespace PetersenCofactor

variable {X : Type}

def pin (b : Bool) (f : Func (X × Bool)) : Func X := fun x => f (x,b)

def pureWire (f : Func (X × Bool)) : Prop :=
  (∃ h : Func Bool, f = fun p => h p.2) ∨ (∃ h : Func X, f = fun p => h p.1)

def applyGate (o : Bool) (a b : Func X) : Func X :=
  fun x => if o then a x || b x else a x && b x

private theorem liftAv {X Y : Type} {W : List (Func X)} {V : List (Func Y)}
    {f : Func X} (e : Y → X) (h : Av W f) (covers : ∀ w ∈ W, Av V (w ∘ e)) :
    Av V (f ∘ e) := by
  induction h with
  | wire hw => exact covers _ hw
  | zero => exact Av.zero
  | one => exact Av.one
  | neg _ ih => exact Av.neg ih

private theorem weaken {V : List (Func X)} {a w : Func X} (h : Av V a) : Av (w :: V) a :=
  liftAv id h (fun _ hv => Av.wire (List.mem_cons_of_mem _ hv))

private theorem availPure {W : List (Func (X × Bool))} {a} (h : Av W a)
    (hw : ∀ w ∈ W, pureWire w) : pureWire a := by
  induction h with
  | wire hv => exact hw _ hv
  | zero => exact Or.inl ⟨fun _ => false,rfl⟩
  | one => exact Or.inl ⟨fun _ => true,rfl⟩
  | neg _ ih =>
    rcases ih with ⟨g,rfl⟩ | ⟨g,rfl⟩
    · exact Or.inl ⟨fun b => !(g b),rfl⟩
    · exact Or.inr ⟨fun x => !(g x),rfl⟩

private theorem constGate {V : List (Func X)} (o c : Bool) {a : Func X} (h : Av V a) :
    Av V (applyGate o (fun _ => c) a) ∧ Av V (applyGate o a (fun _ => c)) := by
  cases o <;> cases c
  · constructor <;> convert (Av.zero (W := V)) using 1 <;> (funext x; simp [applyGate])
  · constructor <;> convert h using 1 <;> (funext x; simp [applyGate])
  · constructor <;> convert h using 1 <;> (funext x; simp [applyGate])
  · constructor <;> convert (Av.one (W := V)) using 1 <;> (funext x; simp [applyGate])

private theorem foldMixed {V : List (Func X)} (b o : Bool) {a d : Func (X × Bool)}
    (ap : pureWire a) (dp : pureWire d) (ha : Av V (pin b a)) (hd : Av V (pin b d))
    (mixed : ¬ pureWire (applyGate o a d)) : Av V (pin b (applyGate o a d)) := by
  rcases ap with ⟨g,rfl⟩ | ⟨g,rfl⟩
  · exact (constGate o (g b) hd).1
  rcases dp with ⟨h,rfl⟩ | ⟨h,rfl⟩
  · exact (constGate o (h b) ha).2
  · exact (mixed (Or.inr ⟨applyGate o g h,rfl⟩)).elim

private theorem pay {I V : List (Func X)} {a d : Func X} {j : Nat} (o : Bool)
    (r : Run I j V) (ha : Av V a) (hd : Av V d) : Run I (j+1) (applyGate o a d :: V) := by
  cases o
  · exact Run.and r ha hd
  · exact Run.or r ha hd

private def Simulation (I : List (Func X)) (b : Bool) (k : Nat)
    (W : List (Func (X × Bool))) : Prop :=
  ∃ j V, Run I j V ∧ (∀ w ∈ W, Av V (pin b w)) ∧ j ≤ k ∧ (j < k ∨ ∀ w ∈ W, pureWire w)

private theorem extend {I : List (Func X)} {b k W} {a d : Func (X × Bool)} (o : Bool)
    (s : Simulation I b k W) (ha : Av W a) (hd : Av W d) :
    Simulation I b (k+1) (applyGate o a d :: W) := by
  obtain ⟨j,V,r,covers,le,caseSplit⟩ := s
  have avA : Av V (pin b a) := liftAv (fun x => (x,b)) ha covers
  have avD : Av V (pin b d) := liftAv (fun x => (x,b)) hd covers
  let new := applyGate o a d
  by_cases save : Av V (pin b new)
  · refine ⟨j,V,r,?_,by omega,Or.inl (by omega)⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hold
    · exact save
    · exact covers _ hold
  · refine ⟨j+1,pin b new :: V,pay o r avA avD,?_,by omega,?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hold
      · exact Av.wire (List.mem_cons_self ..)
      · exact weaken (covers _ hold)
    · rcases caseSplit with cheap | oldPure
      · exact Or.inl (by omega)
      · right
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hold
        · by_contra mixed
          exact save (foldMixed b o (availPure ha oldPure) (availPure hd oldPure) avA avD mixed)
        · exact oldPure _ hold

theorem restrictRun {I : List (Func X)} {W init : List (Func (X × Bool))} {k}
    (b : Bool) (src : Run init k W) (base : ∀ w ∈ init, Av I (pin b w))
    (simple : ∀ w ∈ init, pureWire w) : Simulation I b k W := by
  induction src with
  | start => exact ⟨0,I,Run.start,base,le_refl _,Or.inr simple⟩
  | and _ ha hd ih => exact extend false ih ha hd
  | or _ ha hd ih => exact extend true ih ha hd

/-- In a signed circuit, fixing any input on which a mixed output depends saves a binary gate.
    The remaining initial wires may use constants, copies, and either polarity freely. -/
theorem pin_saves_gate {I : List (Func X)} {W init : List (Func (X × Bool))} {k f}
    (b : Bool) (src : Run init k W) (out : Av W f) (mixed : ¬ pureWire f)
    (base : ∀ w ∈ init, Av I (pin b w)) (simple : ∀ w ∈ init, pureWire w) :
    ∃ j V, j < k ∧ Run I j V ∧ Av V (pin b f) := by
  obtain ⟨j,V,r,covers,_,cases⟩ := restrictRun b src base simple
  exact ⟨j,V,cases.resolve_right (fun h => mixed (availPure out h)),r,
    liftAv (fun x => (x,b)) out covers⟩

def join (f : Func X) : Func (X × Bool) := fun p => f p.1 || p.2

def addInput (I : List (Func X)) : List (Func (X × Bool)) :=
  (fun p => p.2) :: I.map (fun g p => g p.1)

def costAtMost (I : List (Func X)) (f : Func X) (n : Nat) : Prop :=
  ∃ k W, k ≤ n ∧ Run I k W ∧ Av W f

theorem singleton_lower {I : List (Func X)} {f : Func X} (x y : X)
    (hx : f x = false) (hy : f y = true) {n : Nat} (h : costAtMost (addInput I) (join f) n) :
    ∃ k, k < n ∧ costAtMost I f k := by
  obtain ⟨k,W,lk,r,o⟩ := h
  have mixed : ¬ pureWire (join f) := by
    rintro (⟨g,hg⟩ | ⟨g,hg⟩)
    · have e := congrFun hg (x,false)
      have d := congrFun hg (y,false)
      simp [join,hx,hy] at e d
      simp_all
    · have e := congrFun hg (x,false)
      have d := congrFun hg (x,true)
      simp [join,hx] at e d
      simp_all
  have base : ∀ w ∈ addInput I, Av I (pin false w) := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | h
    · exact Av.zero
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp h
    exact Av.wire hg
  have initSimple : ∀ w ∈ addInput I, pureWire w := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | h
    · exact Or.inl ⟨id,rfl⟩
    obtain ⟨g,_,rfl⟩ := List.mem_map.mp h
    exact Or.inr ⟨g,rfl⟩
  obtain ⟨j,V,lt,t,v⟩ := pin_saves_gate false r o mixed base initSimple
  have fold : pin false (join f) = f := by funext u; simp [pin,join]
  rw [fold] at v
  exact ⟨j,by omega,j,V,le_refl _,t,v⟩

end PetersenCofactor
