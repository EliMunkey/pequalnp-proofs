import ThetaAlias
import ThetaL1S0
import ThetaL1S1
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b0_0 : Blocked tgt 10 s0_0 := by
  apply node_sound (nxt := [s1_12,s1_10,a0,s1_17,s1_13,s1_6,a1,s1_18,s1_14,a2,a3,s1_22,s1_15,a4,a5,a6,a7,a8,a9,a10,a11,s1_0,a12,a13,a14,s1_7,a15,a16,s1_16,a17,s1_11,s1_23,a18,a19,a20,a21,a22,a23,a24,a25,a26,s1_1,a27,a28,a29,a30,s1_8,s1_24,a31,a32,s1_9,a33,a34,a35,a36,a37,a38,s1_2,a39,a40,s1_19,a41,a42,s1_25,s1_20,a43,a44,s1_26,s1_21,s1_3,a45,a46,a47,a48,a49,s1_27,a50,s1_4,a51,a52,a53,s1_5,a54,a55])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b1_12
    · exact b1_10
    · exact via sym2 fix2 (by decide +kernel) b1_7
    · exact b1_17
    · exact b1_13
    · exact b1_6
    · exact via sym2 fix2 (by decide +kernel) b1_6
    · exact b1_18
    · exact b1_14
    · exact via sym1 fix1 (by decide +kernel) b1_0
    · exact via sym2 fix2 (by decide +kernel) b1_9
    · exact b1_22
    · exact b1_15
    · exact via sym3 fix3 (by decide +kernel) b1_2
    · exact via sym2 fix2 (by decide +kernel) b1_8
    · exact via sym2 fix2 (by decide +kernel) b1_24
    · exact via sym1 fix1 (by decide +kernel) b1_15
    · exact via sym2 fix2 (by decide +kernel) b1_2
    · exact via sym3 fix3 (by decide +kernel) b1_8
    · exact via sym3 fix3 (by decide +kernel) b1_24
    · exact via sym1 fix1 (by decide +kernel) b1_14
    · exact b1_0
    · exact via sym3 fix3 (by decide +kernel) b1_9
    · exact via sym1 fix1 (by decide +kernel) b1_22
    · exact via sym2 fix2 (by decide +kernel) b1_12
    · exact b1_7
    · exact via sym2 fix2 (by decide +kernel) b1_10
    · exact via sym2 fix2 (by decide +kernel) b1_17
    · exact b1_16
    · exact via sym1 fix1 (by decide +kernel) b1_1
    · exact b1_11
    · exact b1_23
    · exact via sym2 fix2 (by decide +kernel) b1_16
    · exact via sym3 fix3 (by decide +kernel) b1_1
    · exact via sym2 fix2 (by decide +kernel) b1_11
    · exact via sym2 fix2 (by decide +kernel) b1_23
    · exact via sym3 fix3 (by decide +kernel) b1_16
    · exact via sym2 fix2 (by decide +kernel) b1_1
    · exact via sym3 fix3 (by decide +kernel) b1_11
    · exact via sym3 fix3 (by decide +kernel) b1_23
    · exact via sym1 fix1 (by decide +kernel) b1_16
    · exact b1_1
    · exact via sym1 fix1 (by decide +kernel) b1_11
    · exact via sym1 fix1 (by decide +kernel) b1_23
    · exact via sym2 fix2 (by decide +kernel) b1_15
    · exact via sym1 fix1 (by decide +kernel) b1_2
    · exact b1_8
    · exact b1_24
    · exact via sym2 fix2 (by decide +kernel) b1_14
    · exact via sym3 fix3 (by decide +kernel) b1_0
    · exact b1_9
    · exact via sym2 fix2 (by decide +kernel) b1_22
    · exact via sym3 fix3 (by decide +kernel) b1_14
    · exact via sym2 fix2 (by decide +kernel) b1_0
    · exact via sym1 fix1 (by decide +kernel) b1_9
    · exact via sym3 fix3 (by decide +kernel) b1_22
    · exact via sym3 fix3 (by decide +kernel) b1_15
    · exact b1_2
    · exact via sym1 fix1 (by decide +kernel) b1_8
    · exact via sym1 fix1 (by decide +kernel) b1_24
    · exact b1_19
    · exact via sym3 fix3 (by decide +kernel) b1_5
    · exact via sym1 fix1 (by decide +kernel) b1_5
    · exact b1_25
    · exact b1_20
    · exact via sym2 fix2 (by decide +kernel) b1_4
    · exact via sym1 fix1 (by decide +kernel) b1_4
    · exact b1_26
    · exact b1_21
    · exact b1_3
    · exact via sym1 fix1 (by decide +kernel) b1_3
    · exact via sym2 fix2 (by decide +kernel) b1_27
    · exact via sym2 fix2 (by decide +kernel) b1_21
    · exact via sym2 fix2 (by decide +kernel) b1_3
    · exact via sym3 fix3 (by decide +kernel) b1_3
    · exact b1_27
    · exact via sym1 fix1 (by decide +kernel) b1_20
    · exact b1_4
    · exact via sym3 fix3 (by decide +kernel) b1_4
    · exact via sym1 fix1 (by decide +kernel) b1_26
    · exact via sym1 fix1 (by decide +kernel) b1_19
    · exact b1_5
    · exact via sym2 fix2 (by decide +kernel) b1_5
    · exact via sym1 fix1 (by decide +kernel) b1_25
end ThetaCert
