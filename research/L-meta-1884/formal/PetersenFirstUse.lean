import PetersenMinor

open PetersenSignedBridge PetersenFrontier PetersenMinor

namespace PetersenFirstUse

variable {α : Type} [DecidableEq α]

theorem uncons {G : α → α → α → Prop} {I W m c} (tr : Trace G I m c W) :
    (m = 0 ∧ c = 0 ∧ W = I) ∨ ∃ a b o K rest charge,
      a ≠ b ∧ I = insert a (insert b K) ∧ o ∉ I ∧ G a b o ∧
      Trace G (insert o K) rest charge W ∧ rest+1=m ∧ credit a b K + charge=c := by
  induction tr with
  | start => exact Or.inl ⟨rfl,rfl,rfl⟩
  | @step m c K a b o _ distinct fresh g ih =>
    right
    rcases ih with ⟨rfl,rfl,eq⟩ | ⟨x,y,z,B,j,k,ne,ii,fr,op,t,hm,hc⟩
    · subst_vars
      exact ⟨a,b,o,K,0,0,distinct,rfl,fresh,g,Trace.start,rfl,by simp⟩
    · exact ⟨x,y,z,B,j+1,k+credit a b K,ne,ii,fr,op,Trace.step t distinct fresh g,by omega,by omega⟩

noncomputable local instance : DecidableEq (Func PInput) := Classical.decEq _

private theorem source_mem {f : Func PInput} (hf : f ∈ base.toFinset) : ∃ i, vertex i = f :=
  List.mem_ofFn.mp (List.mem_toFinset.mp hf)

def atRow (v : Nat) : PInput := fun i => v.testBit i.val

def pairBase (i j : Fin 10) (value : Bool) : Nat :=
  let pairs : Fin 10 → Fin 10 → Nat × Nat := ![
    ![(0,0),(16,2),(2,20),(2,10),(2,16),(2,32),(2,80),(2,130),(2,258),(2,514)],
    ![(4,1),(0,0),(1,4),(1,9),(1,20),(1,36),(1,64),(1,129),(1,257),(1,513)],
    ![(2,9),(8,2),(0,0),(2,8),(2,18),(2,34),(2,72),(2,128),(2,258),(2,514)],
    ![(4,5),(4,18),(16,4),(0,0),(4,16),(4,36),(4,68),(4,144),(4,256),(4,516)],
    ![(8,1),(1,10),(1,5),(1,8),(0,0),(1,40),(1,65),(1,129),(1,257),(1,512)],
    ![(128,1),(1,130),(1,5),(1,9),(1,144),(0,0),(1,65),(1,128),(1,256),(1,513)],
    ![(2,257),(256,2),(2,260),(2,10),(2,18),(2,34),(0,0),(2,130),(2,256),(2,512)],
    ![(4,5),(4,34),(32,4),(4,40),(4,20),(4,32),(4,68),(0,0),(4,260),(4,512)],
    ![(8,9),(8,10),(8,36),(32,8),(8,48),(8,32),(8,64),(8,136),(0,0),(8,520)],
    ![(16,65),(16,18),(16,20),(16,72),(64,16),(16,48),(16,64),(16,128),(16,272),(0,0)]]
  if value then (pairs i j).2 else (pairs i j).1

def lowerRow (i j : Fin 10) (v : Bool) := atRow (pairBase i j v)
def upperRow (i j : Fin 10) (v : Bool) : PInput :=
  fun h => if h = i then true else lowerRow i j v h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem pivotalPairs : ∀ i j : Fin 10, i ≠ j → ∀ v : Bool,
    lowerRow i j v j = v ∧ upperRow i j v j = v ∧
    PetersenTarget (lowerRow i j v) = false ∧ PetersenTarget (upperRow i j v) = true := by decide

private theorem stable {a b o : Func PInput} (g : PetersenTracePin.gate a b o) (x y : PInput)
    (ha : a x = a y) (hb : b x = b y) : o x = o y := by
  obtain ⟨op,sa,sb,so,rfl⟩ := g
  simp [PetersenTracePin.signed,PetersenCofactor.applyGate,ha,hb]

private theorem neutral {i j : Fin 10} (ne : i ≠ j) (o : Func PInput)
    (g : PetersenTracePin.gate (vertex i) (vertex j) o) :
    ∃ v, o (lowerRow i j v) = o (upperRow i j v) := by
  obtain ⟨op,sa,sb,so,rfl⟩ := g
  let v := if sb then !op else op
  obtain ⟨h1,h2,_,_⟩ := pivotalPairs i j ne v
  refine ⟨v,?_⟩
  simp only [PetersenTracePin.signed,PetersenCofactor.applyGate,vertex,h1,h2]
  cases op <;> cases sb <;> simp [v]

private theorem swapGate {a b o : Func PInput} (g : PetersenTracePin.gate a b o) :
    PetersenTracePin.gate b a o := by
  obtain ⟨op,sa,sb,so,rfl⟩ := g
  refine ⟨op,sb,sa,so,?_⟩
  funext x
  cases op <;> simp [PetersenTracePin.signed,PetersenCofactor.applyGate,Bool.and_comm,Bool.or_comm]


set_option maxRecDepth 12000 in
theorem keepOperand {i j : Fin 10} (ne : i ≠ j) {o K m c}
    (g : PetersenTracePin.gate (vertex i) (vertex j) o) (subset : K ⊆ base.toFinset)
    (tail : Trace PetersenTracePin.gate (insert o K) m c {PetersenTarget}) : vertex i ∈ K := by
  by_contra missing
  obtain ⟨v,he⟩ := neutral ne o g
  let x := lowerRow i j v
  let y := upperRow i j v
  have each : ∀ f ∈ insert o K, f x = f y := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl|h
    · exact he
    · obtain ⟨l,rfl⟩ := source_mem (f := f) (subset h)
      have neq : l ≠ i := fun eq => missing (eq ▸ h)
      simp [vertex,x,y,upperRow,neq]
  have bad := tail.agree x y (fun _ _ _ gg => stable gg x y) each PetersenTarget (Finset.mem_singleton_self _)
  obtain ⟨_,_,v1,v2⟩ := pivotalPairs i j ne v
  exact (Bool.false_ne_true (v1.symm.trans (bad.trans v2)))

set_option maxRecDepth 12000 in
/-- Both first-gate operands must remain live. Fixing the other operand to its canalizing
    value leaves a pivotal pair for each original input, which every suffix has to separate. -/
theorem first_kept {m c} (tr : Trace PetersenTracePin.gate base.toFinset m c {PetersenTarget}) :
    ∃ (i j : Fin 10) (o : Func PInput) (rest charge : Nat),
      i ≠ j ∧ PetersenTracePin.gate (vertex i) (vertex j) o ∧ o ∉ base.toFinset ∧
      Trace PetersenTracePin.gate (insert o base.toFinset) rest charge {PetersenTarget} ∧
      rest+1=m ∧ 2+charge=c := by
  rcases uncons tr with ⟨_,_,eq⟩ | ⟨a,b,o,K,rest,charge,distinct,eq,fr,g,tail,hm,hc⟩
  · have h : ({PetersenTarget} : Finset _).card = base.toFinset.card := congrArg Finset.card eq
    simp [ten_inputs] at h
  · have sub : K ⊆ base.toFinset := by
      rw [eq]; exact fun f h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
    obtain ⟨i,rfl⟩ := source_mem (f := a) (by rw [eq]; exact Finset.mem_insert_self ..)
    obtain ⟨j,rfl⟩ := source_mem (f := b) (by rw [eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have ne : i ≠ j := fun h => distinct (congrArg vertex h)
    have ai := keepOperand ne g sub tail
    have bj := keepOperand ne.symm (swapGate g) sub tail
    have full : K = base.toFinset := by simpa [ai,bj] using eq.symm
    exact ⟨i,j,o,rest,charge,ne,g,fr,full ▸ tail,hm,by simpa [credit,ai,bj] using hc⟩

end PetersenFirstUse
