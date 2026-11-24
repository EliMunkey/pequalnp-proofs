import ThetaAlias
import ThetaL3S4
import ThetaL3S30
import ThetaL3S32
import ThetaL3S43
import ThetaL3S44
import ThetaL3S46
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_600 : Blocked tgt 8 s2_600 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_600 8 _ le
  decide +kernel
theorem b2_601 : Blocked tgt 8 s2_601 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_601 8 _ le
  decide +kernel
theorem b2_602 : Blocked tgt 8 s2_602 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_602 8 _ le
  decide +kernel
theorem b2_603 : Blocked tgt 8 s2_603 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_603 8 _ le
  decide +kernel
theorem b2_604 : Blocked tgt 8 s2_604 := by
  apply node_sound (nxt := [s3_739,a1248,s3_1113,a1249,s3_1038,a1250,s3_1032,a1251,a1252,s3_1034,a1253,a1254,a1255,a1256,s3_1033,s3_1045,a1257,s3_1046,a1258,a1259,s3_1059,s3_100,a1260,s3_782,a1261,s3_1037,a1262,s3_1035])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_739
    · exact via sym2 fix2 (by decide +kernel) b3_739
    · exact b3_1113
    · exact via sym2 fix2 (by decide +kernel) b3_1038
    · exact b3_1038
    · exact via sym2 fix2 (by decide +kernel) b3_1046
    · exact b3_1032
    · exact via sym2 fix2 (by decide +kernel) b3_1033
    · exact via sym2 fix2 (by decide +kernel) b3_1045
    · exact b3_1034
    · exact via sym3 fix3 (by decide +kernel) b3_100
    · exact via sym2 fix2 (by decide +kernel) b3_1059
    · exact via sym2 fix2 (by decide +kernel) b3_100
    · exact via sym3 fix3 (by decide +kernel) b3_1059
    · exact b3_1033
    · exact b3_1045
    · exact via sym2 fix2 (by decide +kernel) b3_1034
    · exact b3_1046
    · exact via sym2 fix2 (by decide +kernel) b3_1032
    · exact via sym1 fix1 (by decide +kernel) b3_100
    · exact b3_1059
    · exact b3_100
    · exact via sym1 fix1 (by decide +kernel) b3_1059
    · exact b3_782
    · exact via sym2 fix2 (by decide +kernel) b3_782
    · exact b3_1037
    · exact via sym2 fix2 (by decide +kernel) b3_1035
    · exact b3_1035
theorem b2_605 : Blocked tgt 8 s2_605 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_605 8 _ le
  decide +kernel
theorem b2_606 : Blocked tgt 8 s2_606 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_606 8 _ le
  decide +kernel
theorem b2_607 : Blocked tgt 8 s2_607 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_607 8 _ le
  decide +kernel
theorem b2_608 : Blocked tgt 8 s2_608 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_608 8 _ le
  decide +kernel
theorem b2_609 : Blocked tgt 8 s2_609 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_609 8 _ le
  decide +kernel
theorem b2_610 : Blocked tgt 8 s2_610 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_610 8 _ le
  decide +kernel
theorem b2_611 : Blocked tgt 8 s2_611 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_611 8 _ le
  decide +kernel
theorem b2_612 : Blocked tgt 8 s2_612 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_612 8 _ le
  decide +kernel
theorem b2_613 : Blocked tgt 8 s2_613 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_613 8 _ le
  decide +kernel
theorem b2_614 : Blocked tgt 8 s2_614 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_614 8 _ le
  decide +kernel
theorem b2_615 : Blocked tgt 8 s2_615 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_615 8 _ le
  decide +kernel
theorem b2_616 : Blocked tgt 8 s2_616 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_616 8 _ le
  decide +kernel
theorem b2_617 : Blocked tgt 8 s2_617 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_617 8 _ le
  decide +kernel
theorem b2_618 : Blocked tgt 8 s2_618 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_618 8 _ le
  decide +kernel
theorem b2_619 : Blocked tgt 8 s2_619 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_619 8 _ le
  decide +kernel
theorem b2_620 : Blocked tgt 8 s2_620 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_620 8 _ le
  decide +kernel
theorem b2_621 : Blocked tgt 8 s2_621 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_621 8 _ le
  decide +kernel
theorem b2_622 : Blocked tgt 8 s2_622 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_622 8 _ le
  decide +kernel
theorem b2_623 : Blocked tgt 8 s2_623 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_623 8 _ le
  decide +kernel
end ThetaCert
