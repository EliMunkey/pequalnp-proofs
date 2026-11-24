import PetersenBank
open PetersenWordCost PetersenFastPin PetersenPackedPin PetersenLayerCheck PetersenBank
namespace PetersenBitBank
variable {w n : Nat}

def Profile (p : View w n) (prog : List Instr) (covered fixed : Nat) : Prop :=
  ∀ i : Fin n, covered.testBit i.val = true →
    (p.cache i).isSome = true ∧
    PetersenForwardSearch.cb (replay p.inputs prog) ((p.cache i).getD 0) = true ∧
    (fixed.testBit i.val = true → isFixed ((p.cache i).getD 0) = true)

def validate (p : View w n) (prog : List Instr) (covered fixed : Nat) : Bool :=
  (List.finRange n).all fun i => !covered.testBit i.val ||
    ((p.cache i).isSome && PetersenForwardSearch.cb (replay p.inputs prog) ((p.cache i).getD 0) &&
      (!fixed.testBit i.val || isFixed ((p.cache i).getD 0)))

theorem certify {p : View w n} {prog covered fixed}
    (ok : validate p prog covered fixed = true) : Profile p prog covered fixed := by
  intro i mem
  have v := List.all_eq_true.mp ok i (by simp)
  simp [mem, Bool.and_eq_true,Bool.or_eq_true] at v
  exact ⟨v.1.1,v.1.2,fun pos => by simpa [pos] using v.2⟩

def fits (covered fixed fuel K cost : Nat) (L : List (Fin n)) : Bool :=
  (L.all fun i => covered.testBit i.val) &&
    decide (cost + fuel < K + 1 + (L.filter fun i => fixed.testBit i.val).toFinset.card)

theorem fit_sound {p : View w n} {word : Fin n → BitVec w} {t} {prog : List Instr} {covered fixed}
    (base : Sound p word t) (inj : Function.Injective word) (profile : Profile p prog covered fixed)
    {L : List (Fin n)} {fuel} (ok : fits covered fixed fuel p.budget prog.length L = true) :
    Blocked t fuel (L.map word) := by
  obtain ⟨avail,num⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨small,hot,values⟩ := base
  have good {i} (hi : i∈L) := profile i (List.all_eq_true.mp avail i hi)
  apply quick_sound values small hot
  apply Bool.and_eq_true_iff.mpr
  refine ⟨List.all_eq_true.mpr (fun i hi => Bool.and_eq_true_iff.mpr ⟨(good hi).1,(good hi).2.1⟩),?_⟩
  apply decide_eq_true
  have sub : ((L.filter fun i => fixed.testBit i.val).toFinset.image word) ⊆
      ((L.filter (fun i => isFixed ((p.cache i).getD 0))).map word).toFinset := by
    intro v hv
    obtain ⟨i,hm,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hi,yes⟩ := List.mem_filter.mp (List.mem_toFinset.mp hm)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,List.mem_filter.mpr ⟨hi,(good hi).2.2 yes⟩,rfl⟩)
  have le := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ inj] at le
  have lt := of_decide_eq_true num
  omega
end PetersenBitBank
