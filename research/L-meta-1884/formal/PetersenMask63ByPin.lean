import PetersenPendant
import PetersenCycleFive
open PetersenWordCost PetersenPendant
namespace PetersenFrontierExamples

theorem cycle_input_words : inputs 5 = PetersenCycleFive.input := by
  let data : Fin 5 → BitVec 32 := ![0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
  have h (i : Fin 5) : pack (fun j : Fin 32 => j.val.testBit i.val) = data i := by
    apply read_inj; rw [read_pack]; funext j; revert i j; decide
  exact (congrArg (fun (f : Fin 5 → BitVec 32) => List.ofFn f) (funext h)).trans (by rfl)

theorem cycle_target_word : graphTarget 5 cycle5 = PetersenCycleFive.target := by
  apply read_inj
  change read (pack _) = read PetersenCycleFive.target
  rw [read_pack]; funext j; revert j; decide

theorem mask63_by_pin : NoAtMost (inputs 6) (graphTarget 6 pendant) 7 := by
  apply mask63_of_cycle5
  rw [cycle_input_words,cycle_target_word]
  exact PetersenCycleFive.no_six_gates

#print axioms mask63_by_pin
end PetersenFrontierExamples
