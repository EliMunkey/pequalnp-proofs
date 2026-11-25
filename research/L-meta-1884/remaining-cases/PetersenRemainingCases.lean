import PetersenReducedStarts
import Petersen22PinSemantics
import SharedK13EarlyFinal
import Petersen22PinWitnesses
import P22M00Final
import P22M41Final
import Petersen22Pin01
open PetersenPhysicalProjection PetersenPhysicalWords Petersen22PinWitnesses
namespace PetersenRemainingCases
def Exact (I : List (BitVec w)) (t : BitVec w) (n : Nat) : Prop :=
  NoPhysical I t (n-1) ∧ ∃W, Positive I n W ∧ t∈W
theorem pin00 : Exact b00 t00 12 := ⟨P22M00Cert.lower,works00⟩
theorem pin01 : Exact b01 t01 8 := ⟨Petersen22Pin01.lower,works01⟩
theorem pin41 : Exact b41 t41 10 := ⟨P22M41Cert.lower,works41⟩
theorem common : PetersenShared22.Hard 13 := SharedK13EarlyCert.lower
theorem full00 : (∀n < 12, ¬PetersenBoundaryCost.Reach Petersen22PinSemantics.base Petersen22PinSemantics.lab00 (Petersen22PinSemantics.known 0 false) n) ∧ PetersenBoundaryCost.Reach Petersen22PinSemantics.base Petersen22PinSemantics.lab00 (Petersen22PinSemantics.known 0 false) 12 := by
  refine ⟨?_,(Petersen22PinSemantics.equivalent00 _).2 pin00.2⟩
  intro n le existsRun
  obtain ⟨W,run,member⟩:=(Petersen22PinSemantics.equivalent00 _).1 existsRun
  exact pin00.1 n (by omega) W run member
theorem full01 : (∀n < 8, ¬PetersenBoundaryCost.Reach Petersen22PinSemantics.base Petersen22PinSemantics.lab01 (Petersen22PinSemantics.known 0 true) n) ∧ PetersenBoundaryCost.Reach Petersen22PinSemantics.base Petersen22PinSemantics.lab01 (Petersen22PinSemantics.known 0 true) 8 := by
  refine ⟨?_,(Petersen22PinSemantics.equivalent01 _).2 pin01.2⟩
  intro n le existsRun
  obtain ⟨W,run,member⟩:=(Petersen22PinSemantics.equivalent01 _).1 existsRun
  exact pin01.1 n (by omega) W run member
theorem full41 : (∀n < 10, ¬PetersenBoundaryCost.Reach Petersen22PinSemantics.base Petersen22PinSemantics.lab41 (Petersen22PinSemantics.known 4 true) n) ∧ PetersenBoundaryCost.Reach Petersen22PinSemantics.base Petersen22PinSemantics.lab41 (Petersen22PinSemantics.known 4 true) 10 := by
  refine ⟨?_,(Petersen22PinSemantics.equivalent41 _).2 pin41.2⟩
  intro n le existsRun
  obtain ⟨W,run,member⟩:=(Petersen22PinSemantics.equivalent41 _).1 existsRun
  exact pin41.1 n (by omega) W run member
theorem upper40 : PetersenBoundaryCost.Reach Petersen22PinSemantics.base Petersen22PinSemantics.lab40 (Petersen22PinSemantics.known 4 false) 13 :=
  (Petersen22PinSemantics.equivalent40 _).2 works40
#print axioms PetersenReducedStarts.original
#print axioms common
#print axioms full00
#print axioms full01
#print axioms full41
#print axioms upper40
end PetersenRemainingCases
