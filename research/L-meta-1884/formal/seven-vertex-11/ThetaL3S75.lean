import ThetaAlias
import ThetaL4S0
import ThetaL4S2
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1800 : Blocked tgt 7 s3_1800 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(4,true))] s3_1800 7 _ le
  decide +kernel
theorem b3_1801 : Blocked tgt 7 s3_1801 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(4,true))] s3_1801 7 _ le
  decide +kernel
theorem b3_1802 : Blocked tgt 7 s3_1802 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s3_1802 7 _ le
  decide +kernel
theorem b3_1803 : Blocked tgt 7 s3_1803 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s3_1803 7 _ le
  decide +kernel
theorem b3_1804 : Blocked tgt 7 s3_1804 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s3_1804 7 _ le
  decide +kernel
theorem b3_1805 : Blocked tgt 7 s3_1805 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s3_1805 7 _ le
  decide +kernel
theorem b3_1806 : Blocked tgt 7 s3_1806 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s3_1806 7 _ le
  decide +kernel
theorem b3_1807 : Blocked tgt 7 s3_1807 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(4,true))] s3_1807 7 _ le
  decide +kernel
theorem b3_1808 : Blocked tgt 7 s3_1808 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(4,true))] s3_1808 7 _ le
  decide +kernel
theorem b3_1809 : Blocked tgt 7 s3_1809 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s3_1809 7 _ le
  decide +kernel
theorem b3_1810 : Blocked tgt 7 s3_1810 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(4,true))] s3_1810 7 _ le
  decide +kernel
theorem b3_1811 : Blocked tgt 7 s3_1811 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s3_1811 7 _ le
  decide +kernel
theorem b3_1812 : Blocked tgt 7 s3_1812 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s3_1812 7 _ le
  decide +kernel
theorem b3_1813 : Blocked tgt 7 s3_1813 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(4,true))] s3_1813 7 _ le
  decide +kernel
theorem b3_1814 : Blocked tgt 7 s3_1814 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,true))] s3_1814 7 _ le
  decide +kernel
theorem b3_1815 : Blocked tgt 7 s3_1815 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true))] s3_1815 7 _ le
  decide +kernel
theorem b3_1816 : Blocked tgt 7 s3_1816 := by
  apply node_sound (nxt := [a2403,a2404])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b4_15
    · exact via sym3 fix3 (by decide +kernel) b4_53
theorem b3_1817 : Blocked tgt 7 s3_1817 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_1817 7 _ le
  decide +kernel
theorem b3_1818 : Blocked tgt 7 s3_1818 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(3,true))] s3_1818 7 _ le
  decide +kernel
theorem b3_1819 : Blocked tgt 7 s3_1819 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(3,true))] s3_1819 7 _ le
  decide +kernel
theorem b3_1820 : Blocked tgt 7 s3_1820 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(4,true))] s3_1820 7 _ le
  decide +kernel
theorem b3_1821 : Blocked tgt 7 s3_1821 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_1821 7 _ le
  decide +kernel
theorem b3_1822 : Blocked tgt 7 s3_1822 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(3,true))] s3_1822 7 _ le
  decide +kernel
theorem b3_1823 : Blocked tgt 7 s3_1823 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(3,true))] s3_1823 7 _ le
  decide +kernel
end ThetaCert
