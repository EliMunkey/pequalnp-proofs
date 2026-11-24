import PetersenDominantPin
open PetersenSignedBridge PetersenFrontier PetersenFrontierSearch PetersenWordCost
open PetersenMonotoneFrontier PetersenPackedPin PetersenDominantPin
namespace PetersenDominantCheck
variable {w u : Nat}

def candidates (W : List (BitVec u)) := (0::W) ++ (0::W).map (~~~·)

theorem av_of_candidate {W : List (BitVec u)} {y} (hy : y∈candidates W) : Av (W.map PetersenWordCost.read) (PetersenWordCost.read y) := by
  have pos (x) (hx:x∈0::W) : Av (W.map PetersenWordCost.read) (PetersenWordCost.read x) := by
    rcases List.mem_cons.mp hx with rfl|h
    · convert Av.zero (W:=W.map PetersenWordCost.read) using 1; funext i; simp [PetersenWordCost.read]
    · exact Av.wire (List.mem_map.mpr ⟨x,h,rfl⟩)
  rcases List.mem_append.mp hy with p|n
  · exact pos y p
  · obtain ⟨x,h,rfl⟩:=List.mem_map.mp n
    convert Av.neg (pos x h) using 1
    funext i; simp [PetersenWordCost.read,i.isLt]

def check (r : Fin u→Fin w) (I : List (BitVec u)) (K : Nat) (t : BitVec w) (p : List Instr)
    (L : List (BitVec w)) (fuel : Nat) : Bool :=
  let q := project r t
  !forced r q t && (L.all fun a => (candidates (replay I p)).any fun v => betterB q (project r a) v) &&
    decide (p.length+fuel < K+1+(L.toFinset.filter (fun a => forced r q a)).card)

theorem append {α : Type*} [DecidableEq α] {G : α→α→α→Prop} {I L T m c d s}
    (p : Trace G I m c L) (q : Tail G L d s T) : Trace G I (m+d) (c+s) T := by
  induction q generalizing m c I with
  | nil => simpa using p
  | step hab fresh g _ ih =>
    have r := ih (Trace.step p hab fresh g)
    convert r using 1 <;> omega

/-- The check on a proposed restriction is exact, independently of any code
which chose the test rows or reconstructed the available smaller-circuit wires. -/
theorem check_sound (r : Fin u→Fin w) (I : List (BitVec u)) (K : Nat) (t : BitVec w) (p : List Instr)
    (L : List (BitVec w)) (fuel : Nat) (small : NoAtMost I (project r t) K)
    (pass : check r I K t p L fuel=true) {m c} (hm:m≤fuel) : ¬Tail Plain L.toFinset m c {t} := by
  intro tail
  obtain ⟨⟨hot,all⟩,num⟩:=Bool.and_eq_true_iff.mp pass |>.imp_left Bool.and_eq_true_iff.mp
  let q:=project r t
  have tr : Trace Plain L.toFinset m c {t} := by simpa using append Trace.start tail
  obtain ⟨j,Z,prog,h,bd⟩:=sufficient tr r q (program_valid I p) (by
    intro a ha
    obtain ⟨v,hv,better⟩:=List.any_eq_true.mp (List.all_eq_true.mp all a (List.mem_toFinset.mp ha))
    exact ⟨v,(better_spec ..).mp better,av_of_candidate hv⟩)
  obtain ⟨v,good,av⟩:=h t (Finset.mem_singleton_self _)
  have eq := sink good
  have fnot : ¬forced r q t=true := by
    intro eq; change (!forced r q t)=true at hot; rw [eq] at hot; exact Bool.noConfusion hot
  have cnt : (({t}:Finset (BitVec w)).filter (fun x=>forced r q x)).card=0 := by simp [fnot]
  rw [cnt,Nat.add_zero] at bd
  have val := of_decide_eq_true num
  change p.length+fuel < K+1+(L.toFinset.filter (fun a=>forced r q a)).card at val
  rw [eq] at av
  exact small j (by omega) Z prog av

#print axioms check_sound
end PetersenDominantCheck
