import PetersenPackedPin
import PetersenLayerCheck

open PetersenPackedPin PetersenWordCost PetersenLayerCheck PetersenFrontierSearch
namespace PetersenFastPin
variable {w u m : Nat}

def valid (r : Fin u → Fin w) (word : Fin m → BitVec w) (tbl : Fin m → Option (BitVec u)) : Prop :=
  ∀ i, match tbl i with
    | none => True
    | some b => b = project r (word i)

def isFixed (v : BitVec u) : Bool := v == 0 || v == ~~~0

def quick (word : Fin m → BitVec w) (tbl : Fin m → Option (BitVec u))
    (I : List (BitVec u)) (K : Nat) (pr : List Instr) (L : List (Fin m)) (fuel : Nat) : Bool :=
  (L.all fun i => (tbl i).isSome && PetersenForwardSearch.cb (replay I pr) ((tbl i).getD 0)) &&
  decide (pr.length + fuel < K + 1 +
    ((L.filter (fun i => isFixed ((tbl i).getD 0))).map word).toFinset.card)

theorem quick_sound {r : Fin u → Fin w} {word : Fin m → BitVec w} {tbl : Fin m → Option (BitVec u)}
    (values : valid r word tbl) {I : List (BitVec u)} {K : Nat} {t : BitVec w}
    (small : NoAtMost I (project r t) K) (hot : forcedConst r t = false)
    {pr : List Instr} {L : List (Fin m)} {fuel : Nat} (yes : quick word tbl I K pr L fuel = true) :
    Blocked t fuel (L.map word) := by
  intro z hz c
  apply rejects_sound r I K t small hot pr (L.map word) fuel _ hz
  obtain ⟨av,lt⟩ := Bool.and_eq_true_iff.mp yes
  have each (i) (hi : i∈L) : (tbl i).getD 0 = project r (word i) ∧
      PetersenForwardSearch.cb (replay I pr) (project r (word i)) = true := by
    obtain ⟨got,cb⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp av i hi)
    have h := values i
    cases eq : tbl i with
    | none => simp [eq] at got
    | some v =>
      simp [eq] at h cb ⊢
      exact ⟨h,h ▸ cb⟩
  have filter : ((L.filter (fun i => isFixed ((tbl i).getD 0))).map word).toFinset =
      (L.map word).toFinset.filter (fun v => forcedConst r v) := by
    ext v
    simp only [List.mem_toFinset,List.mem_map,List.mem_filter,Finset.mem_filter]
    constructor
    · rintro ⟨i,⟨hi,ci⟩,rfl⟩
      exact ⟨⟨i,hi,rfl⟩,by simpa only [isFixed,(each i hi).1,forcedConst] using ci⟩
    · rintro ⟨⟨i,hi,rfl⟩,cv⟩
      exact ⟨i,⟨hi,by simpa only [isFixed,(each i hi).1,forcedConst] using cv⟩,rfl⟩
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact (each i hi).2
  · simpa only [filter] using lt

end PetersenFastPin
