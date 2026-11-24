import PetersenPackedPin

open PetersenPackedPin
namespace PetersenReusableProjection
variable {w u : Nat}

/-- The full specialization of a wire can be proved once and shared between frontier certificates. -/
theorem rejects_of_projection
    (r : Fin u → Fin w) (I : List (BitVec u)) (K : Nat) (program : List Instr)
    (L : List (BitVec w)) (fuel : Nat) (values : List (BitVec u))
    (known : L.map (PetersenPackedPin.project r) = values)
    (nd : L.Nodup)
    (cov : (values.all (PetersenForwardSearch.cb (replay I program))) = true)
    (budget : program.length + fuel < K+1+(values.filter (fun a => a==0 || a==~~~0)).length) :
    rejects r I K program L fuel = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · rw [←known,List.all_map] at cov
    exact cov
  · apply decide_eq_true
    have filt : L.toFinset.filter (fun a => forcedConst r a) = (L.filter (forcedConst r)).toFinset := by
      ext a
      simp
    rw [filt,List.toFinset_card_of_nodup (nd.filter _)]
    rw [← known] at budget
    have num (U : List (BitVec w)) : ((U.map (PetersenPackedPin.project r)).filter
        (fun a => a==0 || a==~~~0)).length = (U.filter (forcedConst r)).length := by
      induction U with
      | nil => rfl
      | cons a U ih =>
        have folded : (PetersenPackedPin.project r a == 0 || PetersenPackedPin.project r a == ~~~0) = forcedConst r a := rfl
        simp only [List.map_cons,List.filter_cons,folded]
        cases val : forcedConst r a <;> simp only [Bool.false_eq_true,ite_false,ite_true,List.length_cons,ih]
    rwa [←num L]

#print axioms rejects_of_projection
end PetersenReusableProjection
