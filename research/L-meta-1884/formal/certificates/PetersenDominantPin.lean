import PetersenMonotoneFrontier
import PetersenPackedPin
open PetersenSignedBridge PetersenFrontier PetersenFrontierSearch PetersenWordCost
open PetersenMonotoneFrontier PetersenPackedPin
namespace PetersenDominantPin
variable {w u : Nat}

/-- An actual physical AND/OR operation without any negated rails. -/
def Plain (a b o : BitVec w) := ∃ op, o = gate op a b

def constWord (v : Bool) : BitVec u := if v then ~~~0 else 0

def betterB (t a b : BitVec u) : Bool := ((a ^^^ b) &&& ~~~(a ^^^ t)) == 0

theorem better_spec (t a b : BitVec u) : betterB t a b=true ↔ Better t a b := by
  rw [betterB,beq_iff_eq]
  constructor
  · intro h i; have eq := congrArg (fun v : BitVec u => v.getLsbD i.val) h
    change ((a ^^^ b) &&& ~~~(a ^^^ t)).getLsbD i.val = (0#u).getLsbD i.val at eq
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,BitVec.getLsbD_zero] at eq
    unfold PetersenWordCost.read; revert eq
    cases a.getLsbD i.val <;> cases b.getLsbD i.val <;> cases t.getLsbD i.val <;> decide
  · intro h; apply read_inj; funext i
    have eq := h i
    unfold PetersenWordCost.read at eq ⊢
    change ((a ^^^ b) &&& ~~~(a ^^^ t)).getLsbD i.val = (0#u).getLsbD i.val
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,BitVec.getLsbD_zero]
    revert eq; cases a.getLsbD i.val <;> cases b.getLsbD i.val <;> cases t.getLsbD i.val <;> decide

def forced (r : Fin u→Fin w) (t : BitVec u) (a : BitVec w) : Bool :=
  betterB t (project r a) 0 || betterB t (project r a) (~~~0)

theorem forced_iff (r : Fin u→Fin w) (t : BitVec u) (a : BitVec w) :
    forced r t a = true ↔ ∃ v, Better t (project r a) (constWord v) := by
  rw [forced,Bool.or_eq_true_iff,better_spec,better_spec]
  constructor
  · rintro (h|h); exact ⟨false,h⟩; exact ⟨true,h⟩
  · rintro ⟨v,h⟩; cases v <;> first | exact Or.inl h | exact Or.inr h

theorem projectGate (r : Fin u→Fin w) (op : Bool) (a b : BitVec w) :
    project r (gate op a b) = gate op (project r a) (project r b) := by
  apply read_inj; funext i
  have ea := congrFun (read_pack (PetersenWordCost.read a ∘ r)) i
  have eb := congrFun (read_pack (PetersenWordCost.read b ∘ r)) i
  rw [project,read_pack]; change PetersenWordCost.read (gate op a b) (r i)=_
  change PetersenWordCost.read (project r a) i=PetersenWordCost.read a (r i) at ea
  change PetersenWordCost.read (project r b) i=PetersenWordCost.read b (r i) at eb
  cases op <;> simp_all [gate,PetersenWordCost.read]

private theorem constGate (op a b : Bool) : gate op (constWord a : BitVec u) (constWord b) =
    constWord (if op then a||b else a&&b) := by cases op <;> cases a <;> cases b <;> simp [gate,constWord]

theorem both (r : Fin u→Fin w) (t : BitVec u) {a b o} (g : Plain a b o)
    (ca : forced r t a) (cb : forced r t b) : forced r t o := by
  obtain ⟨op,rfl⟩:=g; obtain ⟨x,hx⟩:=(forced_iff ..).mp ca; obtain ⟨y,hy⟩:=(forced_iff ..).mp cb
  apply (forced_iff ..).mpr
  refine ⟨if op then x||y else x&&y,?_⟩
  rw [←constGate,projectGate]; exact move op hx hy

def Good (r : Fin u→Fin w) (t : BitVec u) (W : List (Func (Fin u))) (a : BitVec w) :=
  ∃ b, Better t (project r a) b ∧ Av W (PetersenWordCost.read b)

private theorem av_const (W : List (Func (Fin u))) (v : Bool) : Av W (PetersenWordCost.read (constWord v)) := by
  cases v
  · convert Av.zero (W:=W) using 1; funext i; simp [PetersenWordCost.read,constWord]
  · convert Av.one (W:=W) using 1; funext i; simp [PetersenWordCost.read,constWord,i.isLt]

private theorem fold (op v : Bool) {W : List (Func (Fin u))} {b : BitVec u} (hb : Av W (PetersenWordCost.read b)) :
    Av W (PetersenWordCost.read (gate op (constWord v) b)) ∧ Av W (PetersenWordCost.read (gate op b (constWord v))) := by
  have z := av_const W false; have o := av_const W true
  cases op <;> cases v <;> simp_all [gate,constWord]

private theorem weaken {W : List (Func (Fin u))} {a b} (h : Av W a) : Av (b::W) a := by
  induction h with
  | wire h => exact .wire (List.mem_cons_of_mem _ h)
  | zero => exact .zero
  | one => exact .one
  | neg _ ih => exact .neg ih

theorem propagate (r : Fin u→Fin w) (t : BitVec u) {a b o} (g : Plain a b o)
    {I W : List (Func (Fin u))} {j} (p : Run I j W) (aa : Good r t W a) (bb : Good r t W b) :
    ∃ Z, Run I (j+PetersenTracePin.debit (fun v => forced r t v=true) a b) Z ∧
      Good r t Z o ∧ ∀ f, Av W f → Av Z f := by
  obtain ⟨op,rfl⟩:=g
  obtain ⟨x,hx,ax⟩:=aa; obtain ⟨y,hy,ay⟩:=bb
  by_cases save : forced r t a=true ∨ forced r t b=true
  · simp only [PetersenTracePin.debit,ite_eq_left save,Nat.add_zero]
    refine ⟨W,p,?_,fun _ => id⟩
    rcases save with l|q
    · obtain ⟨v,hv⟩:=(forced_iff ..).mp l
      exact ⟨_,projectGate r op a b ▸ move op hv hy,(fold op v ay).1⟩
    · obtain ⟨v,hv⟩:=(forced_iff ..).mp q
      exact ⟨_,projectGate r op a b ▸ move op hx hv,(fold op v ax).2⟩
  · simp only [PetersenTracePin.debit,ite_eq_right save]
    let v := PetersenWordCost.read (gate op x y)
    refine ⟨v::W,?_,⟨_,projectGate r op a b ▸ move op hx hy,Av.wire (List.mem_cons_self ..)⟩,fun _ h=>weaken h⟩
    cases op
    · convert Run.and p ax ay using 2; funext i; simp [v,PetersenWordCost.read,gate]
    · convert Run.or p ax ay using 2; funext i; simp [v,PetersenWordCost.read,gate]

/-- A target-directed optimistic row map may replace a wire by a constant even if
its literal projection is nonconstant. Every such distinct initial live wire
removes a gate upon specialization to a nonconstant target. -/
theorem sufficient {U T : Finset (BitVec w)} {m c : Nat} (run : Trace Plain U m c T)
    (r : Fin u→Fin w) (t : BitVec u) {I W : List (Func (Fin u))} {q}
    (pre : Run I q W) (start : ∀a∈U,Good r t W a) :
    ∃ j Z, Run I j Z ∧ (∀v∈T,Good r t Z v) ∧
      j+(U.filter (fun v=>forced r t v)).card ≤ q+m+(T.filter (fun v=>forced r t v)).card := by
  induction run with
  | start => exact ⟨_,_,pre,start,by omega⟩
  | @step m c K a b o _ ne fresh g ih =>
    obtain ⟨j,Z,p,good,lb⟩:=ih
    obtain ⟨V,prog,out,grow⟩:=propagate r t g p (good a (Finset.mem_insert_self ..))
      (good b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..)))
    have diff := PetersenTracePin.step_budget (fun z=>forced r t z=true) ne fresh (both r t g)
    refine ⟨_,_,prog,?_,by omega⟩
    intro v mem
    rcases Finset.mem_insert.mp mem with rfl|h
    · exact out
    · obtain ⟨y,hy,ay⟩:=good v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
      exact ⟨y,hy,grow _ ay⟩

#print axioms sufficient
end PetersenDominantPin
