import higher.FastGather
open PetersenPackedPin PetersenWordCost
namespace PetersenWireProjection
variable {w u : Nat}

def op (c : Fin 4) (a b : BitVec w) : BitVec w :=
  match c.val with
  | 0 => a &&& b
  | 1 => a &&& ~~~b
  | 2 => (~~~a) &&& b
  | _ => a ||| b

theorem wire_op (r : Fin u → Fin w) (c : Fin 4) (a b : BitVec w) :
    PetersenPackedPin.project r (op c a b) = op c (PetersenPackedPin.project r a) (PetersenPackedPin.project r b) := by
  apply read_inj
  rw [PetersenPackedPin.project,read_pack]
  funext x
  have e := congrFun (read_pack (PetersenWordCost.read a ∘ r)) x
  have f := congrFun (read_pack (PetersenWordCost.read b ∘ r)) x
  change (PetersenPackedPin.project r a).getLsbD x.val = a.getLsbD (r x).val at e
  change (PetersenPackedPin.project r b).getLsbD x.val = b.getLsbD (r x).val at f
  simp [x.isLt,(r x).isLt] at e f
  fin_cases c <;> simp [op,PetersenWordCost.read,e,f,x.isLt,(r x).isLt]

theorem derive {r : Fin u → Fin w} (c : Fin 4) {a b out : BitVec w} {x y v : BitVec u}
    (pa : PetersenPackedPin.project r a = x) (pb : PetersenPackedPin.project r b = y)
    (eq : op c a b = out) (vv : op c x y = v) : PetersenPackedPin.project r out = v := by
  rw [←eq,wire_op,pa,pb,vv]

theorem cons {r : Fin u → Fin w} {a : BitVec w} {v : BitVec u} {l z}
    (head : PetersenPackedPin.project r a = v) (tail : l.map (PetersenPackedPin.project r) = z) :
    (a::l).map (PetersenPackedPin.project r) = v::z := by simp [head,tail]

def small (I : List (BitVec u)) (K : Nat) (p : List Instr) (L : List (BitVec w)) (fuel : Nat)
    (values : List (BitVec u)) : Bool :=
  decide L.Nodup && values.all (PetersenForwardSearch.cb (replay I p)) &&
    decide (p.length+fuel < K+1+(values.filter fun a => a==0 || a==~~~0).length)

theorem reuse (r : Fin u → Fin w) (I : List (BitVec u)) (K : Nat) (p : List Instr)
    (L : List (BitVec w)) (fuel : Nat) (values : List (BitVec u))
    (eq : L.map (PetersenPackedPin.project r) = values) (check : small I K p L fuel values = true) :
    rejects r I K p L fuel = true := by
  obtain ⟨both,limit⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨nd,cov⟩ := Bool.and_eq_true_iff.mp both
  exact PetersenReusableProjection.rejects_of_projection r I K p L fuel values eq
    (of_decide_eq_true nd) cov (of_decide_eq_true limit)

#print axioms wire_op
#print axioms reuse
end PetersenWireProjection
