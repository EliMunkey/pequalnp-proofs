import ThetaAlias
import ThetaL3S0
import ThetaL3S2
import ThetaL3S3
import ThetaL3S6
import ThetaL3S8
import ThetaL3S14
import ThetaL3S18
import ThetaL3S31
import ThetaL3S32
import ThetaL3S33
import ThetaL3S34
import ThetaL3S35
import ThetaL3S36
import ThetaL3S37
import ThetaL3S38
import ThetaL3S49
import ThetaL3S50
import ThetaL3S51
import ThetaL3S53
import ThetaL3S55
import ThetaL3S57
import ThetaL3S62
import ThetaL3S70
import ThetaL3S71
import ThetaL3S72
import ThetaL3S74
import ThetaL3S76
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_552 : Blocked tgt 8 s2_552 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_552 8 _ le
  decide +kernel
theorem b2_553 : Blocked tgt 8 s2_553 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_553 8 _ le
  decide +kernel
theorem b2_554 : Blocked tgt 8 s2_554 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_554 8 _ le
  decide +kernel
theorem b2_555 : Blocked tgt 8 s2_555 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s2_555 8 _ le
  decide +kernel
theorem b2_556 : Blocked tgt 8 s2_556 := by
  apply node_sound (nxt := [s3_799,s3_764,s3_1229,s3_1384,s3_837,s3_752,a1134,s3_1497,s3_3,s3_1778,s3_916,s3_885,a1083,a1135,s3_909,a1136,s3_1696,s3_911,s3_906,a1137,a1138,a1139,s3_907,a1140,a1141,a1142,a1143,s3_76,a1144,a1145,a1146,s3_914,s3_908,s3_912,a1147,a1148,s3_915,s3_440,s3_913])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_799
    · exact b3_764
    · exact b3_1229
    · exact b3_1384
    · exact b3_837
    · exact b3_752
    · exact via sym3 fix3 (by decide +kernel) b3_1220
    · exact b3_1497
    · exact b3_3
    · exact b3_1778
    · exact b3_916
    · exact b3_885
    · exact via sym1 fix1 (by decide +kernel) b3_68
    · exact via sym2 fix2 (by decide +kernel) b3_1290
    · exact b3_909
    · exact via sym1 fix1 (by decide +kernel) b3_1830
    · exact b3_1696
    · exact b3_911
    · exact b3_906
    · exact via sym3 fix3 (by decide +kernel) b3_154
    · exact via sym2 fix2 (by decide +kernel) b3_1275
    · exact via sym2 fix2 (by decide +kernel) b3_1728
    · exact b3_907
    · exact via sym2 fix2 (by decide +kernel) b3_148
    · exact via sym3 fix3 (by decide +kernel) b3_1272
    · exact via sym3 fix3 (by decide +kernel) b3_1731
    · exact via sym1 fix1 (by decide +kernel) b3_877
    · exact b3_76
    · exact via sym3 fix3 (by decide +kernel) b3_1320
    · exact via sym1 fix1 (by decide +kernel) b3_1708
    · exact via sym2 fix2 (by decide +kernel) b3_793
    · exact b3_914
    · exact b3_908
    · exact b3_912
    · exact via sym1 fix1 (by decide +kernel) b3_345
    · exact via sym1 fix1 (by decide +kernel) b3_344
    · exact b3_915
    · exact b3_440
    · exact b3_913
theorem b2_557 : Blocked tgt 8 s2_557 := by
  intro m le c
  apply rejects_sound extra40 i5 4 tgt small40 hot40 [] s2_557 8 _ le
  decide +kernel
theorem b2_558 : Blocked tgt 8 s2_558 := by
  apply node_sound (nxt := [s3_776,s3_768,a1149,s3_1385,s3_847,s3_750,a1120,s3_1496,s3_3,s3_1779,s3_925,s3_885,a1150,a1135,s3_1697,s3_918,a1151,a1152,a1153,s3_919,a1154,a1155,a1156,a1157,s3_77,a1158,a1159,s3_920,s3_923,a1160,s3_924,a1161,s3_926,s3_921,a1162])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_776
    · exact b3_768
    · exact via sym1 fix1 (by decide +kernel) b3_1239
    · exact b3_1385
    · exact b3_847
    · exact b3_750
    · exact via sym2 fix2 (by decide +kernel) b3_1192
    · exact b3_1496
    · exact b3_3
    · exact b3_1779
    · exact b3_925
    · exact b3_885
    · exact via sym1 fix1 (by decide +kernel) b3_71
    · exact via sym2 fix2 (by decide +kernel) b3_1290
    · exact b3_1697
    · exact b3_918
    · exact via sym3 fix3 (by decide +kernel) b3_152
    · exact via sym2 fix2 (by decide +kernel) b3_1276
    · exact via sym2 fix2 (by decide +kernel) b3_1727
    · exact b3_919
    · exact via sym2 fix2 (by decide +kernel) b3_147
    · exact via sym3 fix3 (by decide +kernel) b3_1273
    · exact via sym3 fix3 (by decide +kernel) b3_1730
    · exact via sym1 fix1 (by decide +kernel) b3_878
    · exact b3_77
    · exact via sym3 fix3 (by decide +kernel) b3_1321
    · exact via sym1 fix1 (by decide +kernel) b3_1709
    · exact b3_920
    · exact b3_923
    · exact via sym1 fix1 (by decide +kernel) b3_347
    · exact b3_924
    · exact via sym2 fix2 (by decide +kernel) b3_194
    · exact b3_926
    · exact b3_921
    · exact via sym1 fix1 (by decide +kernel) b3_880
theorem b2_559 : Blocked tgt 8 s2_559 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_559 8 _ le
  decide +kernel
theorem b2_560 : Blocked tgt 8 s2_560 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(1,true))] s2_560 8 _ le
  decide +kernel
theorem b2_561 : Blocked tgt 8 s2_561 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(0,false))] s2_561 8 _ le
  decide +kernel
theorem b2_562 : Blocked tgt 8 s2_562 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s2_562 8 _ le
  decide +kernel
theorem b2_563 : Blocked tgt 8 s2_563 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true))] s2_563 8 _ le
  decide +kernel
theorem b2_564 : Blocked tgt 8 s2_564 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,true))] s2_564 8 _ le
  decide +kernel
theorem b2_565 : Blocked tgt 8 s2_565 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_565 8 _ le
  decide +kernel
theorem b2_566 : Blocked tgt 8 s2_566 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_566 8 _ le
  decide +kernel
theorem b2_567 : Blocked tgt 8 s2_567 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_567 8 _ le
  decide +kernel
theorem b2_568 : Blocked tgt 8 s2_568 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_568 8 _ le
  decide +kernel
theorem b2_569 : Blocked tgt 8 s2_569 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_569 8 _ le
  decide +kernel
theorem b2_570 : Blocked tgt 8 s2_570 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_570 8 _ le
  decide +kernel
theorem b2_571 : Blocked tgt 8 s2_571 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(4,true))] s2_571 8 _ le
  decide +kernel
theorem b2_572 : Blocked tgt 8 s2_572 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,true))] s2_572 8 _ le
  decide +kernel
theorem b2_573 : Blocked tgt 8 s2_573 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true))] s2_573 8 _ le
  decide +kernel
theorem b2_574 : Blocked tgt 8 s2_574 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_574 8 _ le
  decide +kernel
theorem b2_575 : Blocked tgt 8 s2_575 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_575 8 _ le
  decide +kernel
end ThetaCert
