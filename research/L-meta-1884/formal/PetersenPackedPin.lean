import PetersenMinor
import PetersenFrontierSearch
import PetersenForwardSearch

open PetersenSignedBridge PetersenFrontier PetersenPackedFrontier PetersenFrontierSearch
open PetersenWordCost PetersenTracePin

namespace PetersenPackedPin
variable {w u : Nat}
noncomputable local instance {X : Type} : DecidableEq (Func X) := Classical.decEq _
noncomputable local instance {X Y : Type} (r : Y → X) : DecidablePred (constant r) := Classical.decPred _

abbrev Reg := Nat × Bool
abbrev Instr := Bool × Reg × Reg

def argument (W : List (BitVec u)) (a : Reg) : BitVec u :=
  let v := W.getD a.1 0
  if a.2 then ~~~v else v

def applyInstr (W : List (BitVec u)) (i : Instr) : BitVec u :=
  PetersenWordCost.gate i.1 (argument W i.2.1) (argument W i.2.2)

def replay (I : List (BitVec u)) (program : List Instr) : List (BitVec u) :=
  program.foldl (fun W i => applyInstr W i :: W) I

private theorem read_neg (a : BitVec u) : PetersenWordCost.read (~~~a) = fun i => !(PetersenWordCost.read a i) := by
  funext i; simp [PetersenWordCost.read,i.isLt]

private theorem unpack_av {W : List (BitVec u)} {a : BitVec u} (h : Covered W a) : Av (W.map PetersenWordCost.read) (PetersenWordCost.read a) := by
  have direct {v : BitVec u} (hv : v ∈ 0::W) : Av (W.map PetersenWordCost.read) (PetersenWordCost.read v) := by
    rcases List.mem_cons.mp hv with rfl | hw
    · convert (Av.zero (W := W.map PetersenWordCost.read)) using 1; funext i; simp [PetersenWordCost.read]
    · exact Av.wire (List.mem_map.mpr ⟨_,hw,rfl⟩)
  rcases h with h|h
  · exact direct h
  · have n := Av.neg (direct h)
    simpa [read_neg] using n

private theorem arg_ok (W : List (BitVec u)) (a : Reg) : Av (W.map PetersenWordCost.read) (PetersenWordCost.read (argument W a)) := by
  have v : W.getD a.1 0 ∈ 0 :: W := by
    by_cases h : a.1 < W.length
    · rw [List.getD_eq_getElem _ _ h]
      exact List.mem_cons_of_mem _ (List.getElem_mem h)
    · have eq : W.getD a.1 0 = 0 := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : W.length ≤ a.1)]
      rw [eq]; exact List.mem_cons_self ..
  unfold argument
  split
  · rw [read_neg]; exact Av.neg (unpack_av (Or.inl v))
  · exact unpack_av (Or.inl v)

private theorem advance {I W : List (BitVec u)} {j} (pr : Run (I.map PetersenWordCost.read) j (W.map PetersenWordCost.read))
    (i : Instr) : Run (I.map PetersenWordCost.read) (j+1) ((applyInstr W i :: W).map PetersenWordCost.read) := by
  rcases i with ⟨g,a,b⟩
  cases g <;> simp only [List.map_cons]
  · convert Run.and pr (arg_ok W a) (arg_ok W b) using 2
    funext x; simp [applyInstr,PetersenWordCost.gate,PetersenWordCost.read]
  · convert Run.or pr (arg_ok W a) (arg_ok W b) using 2
    funext x; simp [applyInstr,PetersenWordCost.gate,PetersenWordCost.read]

theorem program_valid (I : List (BitVec u)) (p : List Instr) :
    Run (I.map PetersenWordCost.read) p.length ((replay I p).map PetersenWordCost.read) := by
  have general {W j} (run : Run (I.map PetersenWordCost.read) j ((W : List (BitVec u)).map PetersenWordCost.read)) :
      ∀ p : List Instr, Run (I.map PetersenWordCost.read) (j+p.length) ((replay W p).map PetersenWordCost.read) := by
    intro q
    induction q generalizing j W with
    | nil => simpa [replay] using run
    | cons i tail ih =>
      have h := ih (advance run i)
      simpa [replay,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  simpa using general (W := I) Run.start p

def project (r : Fin u → Fin w) (v : BitVec w) : BitVec u := pack (PetersenWordCost.read v ∘ r)

def forcedConst (r : Fin u → Fin w) (v : BitVec w) : Bool :=
  project r v == 0 || project r v == ~~~0

private theorem const_iff (r : Fin u → Fin w) (v : BitVec w) :
    forcedConst r v = true ↔ constant r (PetersenWordCost.read v) := by
  have p := read_pack (PetersenWordCost.read v ∘ r)
  change PetersenWordCost.read (project r v) = _ at p
  simp only [forcedConst,Bool.or_eq_true,beq_iff_eq]
  constructor
  · rintro (a|a)
    · refine ⟨false,?_⟩; rw [←p,a]; funext x; simp [PetersenWordCost.read]
    · refine ⟨true,?_⟩; rw [←p,a]; funext x; simp [PetersenWordCost.read,x.isLt]
  · rintro ⟨b,h⟩
    cases b
    · left; apply read_inj; rw [p,h]; funext x; simp [PetersenWordCost.read]
    · right; apply read_inj; rw [p,h]; funext x; simp [PetersenWordCost.read,x.isLt]

def readEmb (w : Nat) : BitVec w ↪ Func (Fin w) := ⟨PetersenWordCost.read,fun _ _ => read_inj⟩

private theorem gate_complex {a b o : BitVec w} (g : signedWordGate a b o) :
    PetersenTracePin.gate (PetersenWordCost.read a) (PetersenWordCost.read b) (PetersenWordCost.read o) := by
  obtain ⟨⟨p,q⟩,pq,hout⟩ := List.mem_flatMap.mp g
  obtain ⟨hp,hq⟩ := List.mem_product.mp pq
  have sign {p a : BitVec w} (h : p ∈ [a,~~~a]) : ∃ s, PetersenWordCost.read p = PetersenTracePin.signed s (PetersenWordCost.read a) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact ⟨false,rfl⟩
    · exact ⟨true,read_neg _⟩
  have normed (v : BitVec w) : PetersenWordCost.read (norm v) = PetersenTracePin.signed (v.getLsbD 0) (PetersenWordCost.read v) := by
    cases h : v.getLsbD 0
    · rw [show norm v = v by simp [norm,h]]
      rfl
    · rw [show norm v = ~~~v by simp [norm,h]]
      exact read_neg v
  obtain ⟨s,es⟩ := sign hp
  obtain ⟨t,et⟩ := sign hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hout
  rcases hout with rfl|rfl
  · refine ⟨false,s,t,(p &&& q).getLsbD 0,?_⟩; rw [normed,←es,←et]; apply congrArg; funext x
    simp [PetersenWordCost.read,PetersenCofactor.applyGate]
  · refine ⟨true,s,t,(p ||| q).getLsbD 0,?_⟩; rw [normed,←es,←et]; apply congrArg; funext x
    simp [PetersenWordCost.read,PetersenCofactor.applyGate]

private theorem tail_trace {α : Type} [DecidableEq α] {G : α → α → α → Prop}
    {I L T m c d s} (p : Trace G I m c L) (q : Tail G L d s T) : Trace G I (m+d) (c+s) T := by
  induction q generalizing m c I with
  | nil => simpa using p
  | step hab fresh g _ ih =>
    have r := ih (Trace.step p hab fresh g)
    convert r using 1 <;> omega

def rejects (r : Fin u → Fin w) (I : List (BitVec u)) (K : Nat) (program : List Instr)
    (L : List (BitVec w)) (fuel : Nat) : Bool :=
  (L.all fun v => PetersenForwardSearch.cb (replay I program) (project r v)) &&
  decide (program.length + fuel < K + 1 + (L.toFinset.filter (fun x => forcedConst r x)).card)

/-- A successful cut checks a concrete reconstruction of every restricted live signal.
    The certified cost downstairs then rules out every completion at the original frontier. -/
theorem rejects_sound (r : Fin u → Fin w) (I : List (BitVec u)) (K : Nat)
    (t : BitVec w) (small : NoAtMost I (project r t) K) (hot : forcedConst r t = false)
    (program : List Instr) (L : List (BitVec w)) (fuel : Nat) (yes : rejects r I K program L fuel = true)
    {m c} (hm : m ≤ fuel) : ¬ Tail signedWordGate L.toFinset m c {t} := by
  intro q
  have tr : Trace signedWordGate L.toFinset m c {t} := by simpa using tail_trace Trace.start q
  have mapped := map_trace (readEmb w) (fun _ _ _ g => gate_complex g) tr
  rw [Finset.map_singleton] at mapped
  obtain ⟨all,fail⟩ := Bool.and_eq_true_iff.mp yes
  have nc : ¬ constant r (PetersenWordCost.read t) := fun h => Bool.noConfusion (hot.symm.trans ((const_iff r t).mpr h))
  have bound := PetersenTracePin.prune_suffix r mapped (program_valid I program) (by
    intro f hf
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hf
    have cv := PetersenForwardSearch.cb_spec.mp (List.all_eq_true.mp all a (List.mem_toFinset.mp ha))
    have ok := unpack_av cv
    change Av _ (PetersenWordCost.read a ∘ r)
    simpa [project,read_pack] using ok) nc (lower := K+1) (by
      intro j S run a
      by_contra low
      apply small j (by omega) S run
      change Av S (PetersenWordCost.read t ∘ r) at a
      simpa [project,read_pack] using a)
  have filtered : (L.toFinset.map (readEmb w)).filter (constant r) =
      (L.toFinset.filter (fun x => forcedConst r x)).map (readEmb w) := by
    ext f
    constructor
    · intro h
      obtain ⟨old,co⟩ := Finset.mem_filter.mp h
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp old
      exact Finset.mem_map.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,(const_iff r a).mpr co⟩,rfl⟩
    · intro h
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp h
      obtain ⟨ha,co⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨_,ha,rfl⟩,(const_iff r a).mp co⟩
  rw [filtered,Finset.card_map] at bound
  have bad := of_decide_eq_true fail
  omega

end PetersenPackedPin
