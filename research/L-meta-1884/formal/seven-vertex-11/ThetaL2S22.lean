import ThetaAlias
import ThetaL3S0
import ThetaL3S3
import ThetaL3S5
import ThetaL3S31
import ThetaL3S32
import ThetaL3S33
import ThetaL3S35
import ThetaL3S36
import ThetaL3S49
import ThetaL3S51
import ThetaL3S57
import ThetaL3S62
import ThetaL3S64
import ThetaL3S70
import ThetaL3S71
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_528 : Blocked tgt 8 s2_528 := by
  apply node_sound (nxt := [s3_799,s3_760,s3_1229,s3_1383,s3_847,s3_745,a1120,s3_1494,s3_3,s3_1544,s3_867,s3_861,a1121,a1122,s3_1698,s3_862,a1123,a1124,a1125,a1126,a1127,a1128,a1129,a1130,s3_73,a1131,a1132,a1133,s3_865,s3_863,s3_866])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_799
    · exact b3_760
    · exact b3_1229
    · exact b3_1383
    · exact b3_847
    · exact b3_745
    · exact via sym2 fix2 (by decide +kernel) b3_1192
    · exact b3_1494
    · exact b3_3
    · exact b3_1544
    · exact b3_867
    · exact b3_861
    · exact via sym1 fix1 (by decide +kernel) b3_73
    · exact via sym2 fix2 (by decide +kernel) b3_1381
    · exact b3_1698
    · exact b3_862
    · exact via sym3 fix3 (by decide +kernel) b3_138
    · exact via sym2 fix2 (by decide +kernel) b3_1380
    · exact via sym2 fix2 (by decide +kernel) b3_1726
    · exact via sym1 fix1 (by decide +kernel) b3_862
    · exact via sym2 fix2 (by decide +kernel) b3_138
    · exact via sym3 fix3 (by decide +kernel) b3_1380
    · exact via sym3 fix3 (by decide +kernel) b3_1726
    · exact via sym1 fix1 (by decide +kernel) b3_861
    · exact b3_73
    · exact via sym3 fix3 (by decide +kernel) b3_1381
    · exact via sym1 fix1 (by decide +kernel) b3_1698
    · exact via sym2 fix2 (by decide +kernel) b3_791
    · exact b3_865
    · exact b3_863
    · exact b3_866
theorem b2_529 : Blocked tgt 8 s2_529 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_529 8 _ le
  decide +kernel
theorem b2_530 : Blocked tgt 8 s2_530 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(1,true))] s2_530 8 _ le
  decide +kernel
theorem b2_531 : Blocked tgt 8 s2_531 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(0,false))] s2_531 8 _ le
  decide +kernel
theorem b2_532 : Blocked tgt 8 s2_532 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s2_532 8 _ le
  decide +kernel
theorem b2_533 : Blocked tgt 8 s2_533 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true))] s2_533 8 _ le
  decide +kernel
theorem b2_534 : Blocked tgt 8 s2_534 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,true))] s2_534 8 _ le
  decide +kernel
theorem b2_535 : Blocked tgt 8 s2_535 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_535 8 _ le
  decide +kernel
theorem b2_536 : Blocked tgt 8 s2_536 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_536 8 _ le
  decide +kernel
theorem b2_537 : Blocked tgt 8 s2_537 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_537 8 _ le
  decide +kernel
theorem b2_538 : Blocked tgt 8 s2_538 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_538 8 _ le
  decide +kernel
theorem b2_539 : Blocked tgt 8 s2_539 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_539 8 _ le
  decide +kernel
theorem b2_540 : Blocked tgt 8 s2_540 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_540 8 _ le
  decide +kernel
theorem b2_541 : Blocked tgt 8 s2_541 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(4,true))] s2_541 8 _ le
  decide +kernel
theorem b2_542 : Blocked tgt 8 s2_542 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,true))] s2_542 8 _ le
  decide +kernel
theorem b2_543 : Blocked tgt 8 s2_543 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true))] s2_543 8 _ le
  decide +kernel
theorem b2_544 : Blocked tgt 8 s2_544 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_544 8 _ le
  decide +kernel
theorem b2_545 : Blocked tgt 8 s2_545 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_545 8 _ le
  decide +kernel
theorem b2_546 : Blocked tgt 8 s2_546 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_546 8 _ le
  decide +kernel
theorem b2_547 : Blocked tgt 8 s2_547 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(3,true))] s2_547 8 _ le
  decide +kernel
theorem b2_548 : Blocked tgt 8 s2_548 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(3,true))] s2_548 8 _ le
  decide +kernel
theorem b2_549 : Blocked tgt 8 s2_549 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(3,true))] s2_549 8 _ le
  decide +kernel
theorem b2_550 : Blocked tgt 8 s2_550 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_550 8 _ le
  decide +kernel
theorem b2_551 : Blocked tgt 8 s2_551 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_551 8 _ le
  decide +kernel
end ThetaCert
