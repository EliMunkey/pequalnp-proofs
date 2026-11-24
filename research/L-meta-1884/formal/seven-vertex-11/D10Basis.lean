import PetersenComponentLifts
import PetersenPackedPin
import PetersenLayerCheck
import M189Closing
import Extra191
open PetersenPackedPin PetersenWordCost PetersenLayerCheck
namespace Deleted191Cost10
set_option maxRecDepth 200000
set_option maxHeartbeats 0
def tgt : BitVec 128 := 0xfffffffffffaf8f8ffeafaeaffeaf8c8
def cycle0 (r : Fin 32) : Fin 128 := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] : Array (Fin 128))[r.val]?.getD 0
def i5 : List (BitVec 32) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
theorem small0 : NoAtMost i5 (PetersenPackedPin.project cycle0 tgt) 6 := by
  have h : PetersenPackedPin.project cycle0 tgt = (0xffeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact PetersenCycleFive.no_six_gates
theorem hot0 : forcedConst cycle0 tgt = false := by decide +kernel
def cycle1 (r : Fin 32) : Fin 128 := (#[0,1,2,3,4,5,6,7,64,65,66,67,68,69,70,71,32,33,34,35,36,37,38,39,96,97,98,99,100,101,102,103] : Array (Fin 128))[r.val]?.getD 0

theorem small1 : NoAtMost i5 (PetersenPackedPin.project cycle1 tgt) 6 := by
  have h : PetersenPackedPin.project cycle1 tgt = (0xffeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact PetersenCycleFive.no_six_gates
theorem hot1 : forcedConst cycle1 tgt = false := by decide +kernel
def pendant2 (r : Fin 64) : Fin 128 := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63] : Array (Fin 128))[r.val]?.getD 0
def i6 : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
theorem small2 : NoAtMost i6 (PetersenPackedPin.project pendant2 tgt) 7 := by
  have h : PetersenPackedPin.project pendant2 tgt = (0xffeafaeaffeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact PetersenGraphCosts.mask63_exact_lower
theorem hot2 : forcedConst pendant2 tgt = false := by decide +kernel
def pendant3 (r : Fin 64) : Fin 128 := (#[0,4,2,6,1,5,3,7,16,20,18,22,17,21,19,23,8,12,10,14,9,13,11,15,24,28,26,30,25,29,27,31,64,68,66,70,65,69,67,71,80,84,82,86,81,85,83,87,72,76,74,78,73,77,75,79,88,92,90,94,89,93,91,95] : Array (Fin 128))[r.val]?.getD 0

theorem small3 : NoAtMost i6 (PetersenPackedPin.project pendant3 tgt) 7 := by
  have h : PetersenPackedPin.project pendant3 tgt = (0xffeafaeaffeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact PetersenGraphCosts.mask63_exact_lower
theorem hot3 : forcedConst pendant3 tgt = false := by decide +kernel
def pendant4 (r : Fin 64) : Fin 128 := (#[0,4,2,6,1,5,3,7,32,36,34,38,33,37,35,39,64,68,66,70,65,69,67,71,96,100,98,102,97,101,99,103,8,12,10,14,9,13,11,15,40,44,42,46,41,45,43,47,72,76,74,78,73,77,75,79,104,108,106,110,105,109,107,111] : Array (Fin 128))[r.val]?.getD 0

theorem small4 : NoAtMost i6 (PetersenPackedPin.project pendant4 tgt) 7 := by
  have h : PetersenPackedPin.project pendant4 tgt = (0xffeafaeaffeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact PetersenGraphCosts.mask63_exact_lower
theorem hot4 : forcedConst pendant4 tgt = false := by decide +kernel
def pendant5 (r : Fin 64) : Fin 128 := (#[0,1,2,3,4,5,6,7,64,65,66,67,68,69,70,71,32,33,34,35,36,37,38,39,96,97,98,99,100,101,102,103,16,17,18,19,20,21,22,23,80,81,82,83,84,85,86,87,48,49,50,51,52,53,54,55,112,113,114,115,116,117,118,119] : Array (Fin 128))[r.val]?.getD 0

theorem small5 : NoAtMost i6 (PetersenPackedPin.project pendant5 tgt) 7 := by
  have h : PetersenPackedPin.project pendant5 tgt = (0xffeafaeaffeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact PetersenGraphCosts.mask63_exact_lower
theorem hot5 : forcedConst pendant5 tgt = false := by decide +kernel
def tree6 (r : Fin 64) : Fin 128 := (#[0,16,1,17,32,48,33,49,64,80,65,81,96,112,97,113,8,24,9,25,40,56,41,57,72,88,73,89,104,120,105,121,2,18,3,19,34,50,35,51,66,82,67,83,98,114,99,115,10,26,11,27,42,58,43,59,74,90,75,91,106,122,107,123] : Array (Fin 128))[r.val]?.getD 0

theorem small6 : NoAtMost i6 (PetersenPackedPin.project tree6 tgt) 6 := by
  have h : PetersenPackedPin.project tree6 tgt = (0xfeeefcccfaeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact PetersenGraphCosts.M111.bound
theorem hot6 : forcedConst tree6 tgt = false := by decide +kernel
def tree7 (r : Fin 64) : Fin 128 := (#[0,8,4,12,64,72,68,76,32,40,36,44,96,104,100,108,16,24,20,28,80,88,84,92,48,56,52,60,112,120,116,124,2,10,6,14,66,74,70,78,34,42,38,46,98,106,102,110,18,26,22,30,82,90,86,94,50,58,54,62,114,122,118,126] : Array (Fin 128))[r.val]?.getD 0

theorem small7 : NoAtMost i6 (PetersenPackedPin.project tree7 tgt) 6 := by
  have h : PetersenPackedPin.project tree7 tgt = (0xfeeefcccfaeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact PetersenGraphCosts.M111.bound
theorem hot7 : forcedConst tree7 tgt = false := by decide +kernel
def hex8 (r : Fin 64) : Fin 128 := (#[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61,64,65,68,69,72,73,76,77,80,81,84,85,88,89,92,93,96,97,100,101,104,105,108,109,112,113,116,117,120,121,124,125] : Array (Fin 128))[r.val]?.getD 0

theorem small8 : NoAtMost i6 (PetersenPackedPin.project hex8 tgt) 7 := by
  have h : PetersenPackedPin.project hex8 tgt = (0xfffffeccfaeafac0 : BitVec 64) := by decide +kernel
  rw [h]; exact M189Certificate.lower
theorem hot8 : forcedConst hex8 tgt = false := by decide +kernel
def extra9 (r : Fin 64) : Fin 128 := (#[1,9,5,13,65,73,69,77,3,11,7,15,67,75,71,79,17,25,21,29,81,89,85,93,19,27,23,31,83,91,87,95,33,41,37,45,97,105,101,109,35,43,39,47,99,107,103,111,49,57,53,61,113,121,117,125,51,59,55,63,115,123,119,127] : Array (Fin 128))[r.val]?.getD 0

theorem small9 : NoAtMost i6 (PetersenPackedPin.project extra9 tgt) 4 := by
  have h : PetersenPackedPin.project extra9 tgt = (0xffffffffffffffc8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra191.b7_3
theorem hot9 : forcedConst extra9 tgt = false := by decide +kernel
def extra10 (r : Fin 64) : Fin 128 := (#[2,10,34,42,66,74,98,106,18,26,50,58,82,90,114,122,3,11,35,43,67,75,99,107,19,27,51,59,83,91,115,123,6,14,38,46,70,78,102,110,22,30,54,62,86,94,118,126,7,15,39,47,71,79,103,111,23,31,55,63,87,95,119,127] : Array (Fin 128))[r.val]?.getD 0

theorem small10 : NoAtMost i6 (PetersenPackedPin.project extra10 tgt) 4 := by
  have h : PetersenPackedPin.project extra10 tgt = (0xffffffffffffeac0 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra191.b45_2
theorem hot10 : forcedConst extra10 tgt = false := by decide +kernel
def extra11 (r : Fin 64) : Fin 128 := (#[4,20,5,21,36,52,37,53,6,22,7,23,38,54,39,55,12,28,13,29,44,60,45,61,14,30,15,31,46,62,47,63,68,84,69,85,100,116,101,117,70,86,71,87,102,118,103,119,76,92,77,93,108,124,109,125,78,94,79,95,110,126,111,127] : Array (Fin 128))[r.val]?.getD 0

theorem small11 : NoAtMost i6 (PetersenPackedPin.project extra11 tgt) 4 := by
  have h : PetersenPackedPin.project extra11 tgt = (0xffffffffffffffc8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra191.b7_3
theorem hot11 : forcedConst extra11 tgt = false := by decide +kernel
def extra12 (r : Fin 64) : Fin 128 := (#[8,10,9,11,40,42,41,43,72,74,73,75,104,106,105,107,12,14,13,15,44,46,45,47,76,78,77,79,108,110,109,111,24,26,25,27,56,58,57,59,88,90,89,91,120,122,121,123,28,30,29,31,60,62,61,63,92,94,93,95,124,126,125,127] : Array (Fin 128))[r.val]?.getD 0

theorem small12 : NoAtMost i6 (PetersenPackedPin.project extra12 tgt) 5 := by
  have h : PetersenPackedPin.project extra12 tgt = (0xfffffffffffff8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra191.b15_2
theorem hot12 : forcedConst extra12 tgt = false := by decide +kernel
def extra13 (r : Fin 64) : Fin 128 := (#[16,18,20,22,80,82,84,86,48,50,52,54,112,114,116,118,17,19,21,23,81,83,85,87,49,51,53,55,113,115,117,119,24,26,28,30,88,90,92,94,56,58,60,62,120,122,124,126,25,27,29,31,89,91,93,95,57,59,61,63,121,123,125,127] : Array (Fin 128))[r.val]?.getD 0

theorem small13 : NoAtMost i6 (PetersenPackedPin.project extra13 tgt) 5 := by
  have h : PetersenPackedPin.project extra13 tgt = (0xfffffffffffff8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra191.b15_2
theorem hot13 : forcedConst extra13 tgt = false := by decide +kernel
def extra14 (r : Fin 64) : Fin 128 := (#[32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,33,35,37,39,41,43,45,47,49,51,53,55,57,59,61,63,96,98,100,102,104,106,108,110,112,114,116,118,120,122,124,126,97,99,101,103,105,107,109,111,113,115,117,119,121,123,125,127] : Array (Fin 128))[r.val]?.getD 0

theorem small14 : NoAtMost i6 (PetersenPackedPin.project extra14 tgt) 5 := by
  have h : PetersenPackedPin.project extra14 tgt = (0xfffffffffffff8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra191.b15_2
theorem hot14 : forcedConst extra14 tgt = false := by decide +kernel
def extra15 (r : Fin 64) : Fin 128 := (#[64,66,65,67,80,82,81,83,72,74,73,75,88,90,89,91,68,70,69,71,84,86,85,87,76,78,77,79,92,94,93,95,96,98,97,99,112,114,113,115,104,106,105,107,120,122,121,123,100,102,101,103,116,118,117,119,108,110,109,111,124,126,125,127] : Array (Fin 128))[r.val]?.getD 0

theorem small15 : NoAtMost i6 (PetersenPackedPin.project extra15 tgt) 5 := by
  have h : PetersenPackedPin.project extra15 tgt = (0xfffffffffffff8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra191.b15_2
theorem hot15 : forcedConst extra15 tgt = false := by decide +kernel
def extra16 (r : Fin 32) : Fin 128 := (#[0,8,4,12,64,72,68,76,32,40,36,44,96,104,100,108,16,24,20,28,80,88,84,92,48,56,52,60,112,120,116,124] : Array (Fin 128))[r.val]?.getD 0

theorem small16 : NoAtMost i5 (PetersenPackedPin.project extra16 tgt) 4 := by
  have h : PetersenPackedPin.project extra16 tgt = (0xfaeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b47_0
theorem hot16 : forcedConst extra16 tgt = false := by decide +kernel
def extra17 (r : Fin 32) : Fin 128 := (#[2,10,34,42,66,74,98,106,18,26,50,58,82,90,114,122,6,14,38,46,70,78,102,110,22,30,54,62,86,94,118,126] : Array (Fin 128))[r.val]?.getD 0

theorem small17 : NoAtMost i5 (PetersenPackedPin.project extra17 tgt) 3 := by
  have h : PetersenPackedPin.project extra17 tgt = (0xffffeac0 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b45_1
theorem hot17 : forcedConst extra17 tgt = false := by decide +kernel
def extra18 (r : Fin 32) : Fin 128 := (#[1,9,5,13,65,73,69,77,17,25,21,29,81,89,85,93,33,41,37,45,97,105,101,109,49,57,53,61,113,121,117,125] : Array (Fin 128))[r.val]?.getD 0

theorem small18 : NoAtMost i5 (PetersenPackedPin.project extra18 tgt) 3 := by
  have h : PetersenPackedPin.project extra18 tgt = (0xffffffc8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b7_2
theorem hot18 : forcedConst extra18 tgt = false := by decide +kernel
def extra19 (r : Fin 16) : Fin 128 := (#[0,8,32,40,64,72,96,104,16,24,48,56,80,88,112,120] : Array (Fin 128))[r.val]?.getD 0
def i4 : List (BitVec 16) := [0xaaaa,0xcccc,0xf0f0,0xff00]
theorem small19 : NoAtMost i4 (PetersenPackedPin.project extra19 tgt) 2 := by
  have h : PetersenPackedPin.project extra19 tgt = (0xeac0 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b45_0
theorem hot19 : forcedConst extra19 tgt = false := by decide +kernel
def extra20 (r : Fin 8) : Fin 128 := (#[4,6,12,14,68,70,76,78] : Array (Fin 128))[r.val]?.getD 0
def i3 : List (BitVec 8) := [0xaa,0xcc,0xf0]
theorem small20 : NoAtMost i3 (PetersenPackedPin.project extra20 tgt) 1 := by
  have h : PetersenPackedPin.project extra20 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot20 : forcedConst extra20 tgt = false := by decide +kernel
def extra21 (r : Fin 8) : Fin 128 := (#[1,3,17,19,33,35,49,51] : Array (Fin 128))[r.val]?.getD 0

theorem small21 : NoAtMost i3 (PetersenPackedPin.project extra21 tgt) 1 := by
  have h : PetersenPackedPin.project extra21 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot21 : forcedConst extra21 tgt = false := by decide +kernel
def extra22 (r : Fin 32) : Fin 128 := (#[5,7,13,15,21,23,29,31,37,39,45,47,53,55,61,63,69,71,77,79,85,87,93,95,101,103,109,111,117,119,125,127] : Array (Fin 128))[r.val]?.getD 0

theorem small22 : NoAtMost i5 (PetersenPackedPin.project extra22 tgt) 3 := by
  have h : PetersenPackedPin.project extra22 tgt = (0xfffffffe : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b0_5
theorem hot22 : forcedConst extra22 tgt = false := by decide +kernel
def extra23 (r : Fin 16) : Fin 128 := (#[0,2,4,6,64,66,68,70,32,34,36,38,96,98,100,102] : Array (Fin 128))[r.val]?.getD 0

theorem small23 : NoAtMost i4 (PetersenPackedPin.project extra23 tgt) 3 := by
  have h : PetersenPackedPin.project extra23 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot23 : forcedConst extra23 tgt = false := by decide +kernel
def extra24 (r : Fin 16) : Fin 128 := (#[8,40,72,104,12,44,76,108,24,56,88,120,28,60,92,124] : Array (Fin 128))[r.val]?.getD 0

theorem small24 : NoAtMost i4 (PetersenPackedPin.project extra24 tgt) 2 := by
  have h : PetersenPackedPin.project extra24 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot24 : forcedConst extra24 tgt = false := by decide +kernel
def extra25 (r : Fin 32) : Fin 128 := (#[1,5,65,69,3,7,67,71,17,21,81,85,19,23,83,87,33,37,97,101,35,39,99,103,49,53,113,117,51,55,115,119] : Array (Fin 128))[r.val]?.getD 0

theorem small25 : NoAtMost i5 (PetersenPackedPin.project extra25 tgt) 3 := by
  have h : PetersenPackedPin.project extra25 tgt = (0xfffffff8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b3_3
theorem hot25 : forcedConst extra25 tgt = false := by decide +kernel
def extra26 (r : Fin 16) : Fin 128 := (#[9,11,13,15,25,27,29,31,41,43,45,47,57,59,61,63] : Array (Fin 128))[r.val]?.getD 0

theorem small26 : NoAtMost i4 (PetersenPackedPin.project extra26 tgt) 2 := by
  have h : PetersenPackedPin.project extra26 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot26 : forcedConst extra26 tgt = false := by decide +kernel
def extra27 (r : Fin 32) : Fin 128 := (#[0,4,64,68,32,36,96,100,2,6,66,70,34,38,98,102,8,12,72,76,40,44,104,108,10,14,74,78,42,46,106,110] : Array (Fin 128))[r.val]?.getD 0

theorem small27 : NoAtMost i5 (PetersenPackedPin.project extra27 tgt) 4 := by
  have h : PetersenPackedPin.project extra27 tgt = (0xeaeaeac8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b55_0
theorem hot27 : forcedConst extra27 tgt = false := by decide +kernel
def extra28 (r : Fin 32) : Fin 128 := (#[16,18,20,22,80,82,84,86,48,50,52,54,112,114,116,118,24,26,28,30,88,90,92,94,56,58,60,62,120,122,124,126] : Array (Fin 128))[r.val]?.getD 0

theorem small28 : NoAtMost i5 (PetersenPackedPin.project extra28 tgt) 4 := by
  have h : PetersenPackedPin.project extra28 tgt = (0xfffff8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b15_1
theorem hot28 : forcedConst extra28 tgt = false := by decide +kernel
def extra29 (r : Fin 32) : Fin 128 := (#[1,9,5,13,65,73,69,77,3,11,7,15,67,75,71,79,33,41,37,45,97,105,101,109,35,43,39,47,99,107,103,111] : Array (Fin 128))[r.val]?.getD 0

theorem small29 : NoAtMost i5 (PetersenPackedPin.project extra29 tgt) 3 := by
  have h : PetersenPackedPin.project extra29 tgt = (0xffffffc8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b7_2
theorem hot29 : forcedConst extra29 tgt = false := by decide +kernel
def extra30 (r : Fin 32) : Fin 128 := (#[0,4,8,12,16,20,24,28,2,6,10,14,18,22,26,30,64,68,72,76,80,84,88,92,66,70,74,78,82,86,90,94] : Array (Fin 128))[r.val]?.getD 0

theorem small30 : NoAtMost i5 (PetersenPackedPin.project extra30 tgt) 4 := by
  have h : PetersenPackedPin.project extra30 tgt = (0xeaeaeac8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b55_0
theorem hot30 : forcedConst extra30 tgt = false := by decide +kernel
def extra31 (r : Fin 32) : Fin 128 := (#[32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,96,98,100,102,104,106,108,110,112,114,116,118,120,122,124,126] : Array (Fin 128))[r.val]?.getD 0

theorem small31 : NoAtMost i5 (PetersenPackedPin.project extra31 tgt) 4 := by
  have h : PetersenPackedPin.project extra31 tgt = (0xfffff8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b15_1
theorem hot31 : forcedConst extra31 tgt = false := by decide +kernel
def extra32 (r : Fin 32) : Fin 128 := (#[1,9,5,13,65,73,69,77,3,11,7,15,67,75,71,79,17,25,21,29,81,89,85,93,19,27,23,31,83,91,87,95] : Array (Fin 128))[r.val]?.getD 0

theorem small32 : NoAtMost i5 (PetersenPackedPin.project extra32 tgt) 3 := by
  have h : PetersenPackedPin.project extra32 tgt = (0xffffffc8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b7_2
theorem hot32 : forcedConst extra32 tgt = false := by decide +kernel
def extra33 (r : Fin 16) : Fin 128 := (#[0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30] : Array (Fin 128))[r.val]?.getD 0

theorem small33 : NoAtMost i4 (PetersenPackedPin.project extra33 tgt) 3 := by
  have h : PetersenPackedPin.project extra33 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot33 : forcedConst extra33 tgt = false := by decide +kernel
def extra34 (r : Fin 16) : Fin 128 := (#[64,72,80,88,68,76,84,92,96,104,112,120,100,108,116,124] : Array (Fin 128))[r.val]?.getD 0

theorem small34 : NoAtMost i4 (PetersenPackedPin.project extra34 tgt) 2 := by
  have h : PetersenPackedPin.project extra34 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot34 : forcedConst extra34 tgt = false := by decide +kernel
def extra35 (r : Fin 32) : Fin 128 := (#[1,5,9,13,3,7,11,15,17,21,25,29,19,23,27,31,33,37,41,45,35,39,43,47,49,53,57,61,51,55,59,63] : Array (Fin 128))[r.val]?.getD 0

theorem small35 : NoAtMost i5 (PetersenPackedPin.project extra35 tgt) 3 := by
  have h : PetersenPackedPin.project extra35 tgt = (0xfffffff8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b3_3
theorem hot35 : forcedConst extra35 tgt = false := by decide +kernel
def extra36 (r : Fin 16) : Fin 128 := (#[65,67,69,71,81,83,85,87,97,99,101,103,113,115,117,119] : Array (Fin 128))[r.val]?.getD 0

theorem small36 : NoAtMost i4 (PetersenPackedPin.project extra36 tgt) 2 := by
  have h : PetersenPackedPin.project extra36 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot36 : forcedConst extra36 tgt = false := by decide +kernel
def extra37 (r : Fin 32) : Fin 128 := (#[0,16,1,17,32,48,33,49,64,80,65,81,96,112,97,113,8,24,9,25,40,56,41,57,72,88,73,89,104,120,105,121] : Array (Fin 128))[r.val]?.getD 0

theorem small37 : NoAtMost i5 (PetersenPackedPin.project extra37 tgt) 4 := by
  have h : PetersenPackedPin.project extra37 tgt = (0xfaeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b47_0
theorem hot37 : forcedConst extra37 tgt = false := by decide +kernel
def extra38 (r : Fin 32) : Fin 128 := (#[4,20,5,21,36,52,37,53,12,28,13,29,44,60,45,61,68,84,69,85,100,116,101,117,76,92,77,93,108,124,109,125] : Array (Fin 128))[r.val]?.getD 0

theorem small38 : NoAtMost i5 (PetersenPackedPin.project extra38 tgt) 3 := by
  have h : PetersenPackedPin.project extra38 tgt = (0xffffffc8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b7_2
theorem hot38 : forcedConst extra38 tgt = false := by decide +kernel
def extra39 (r : Fin 32) : Fin 128 := (#[2,10,34,42,66,74,98,106,18,26,50,58,82,90,114,122,3,11,35,43,67,75,99,107,19,27,51,59,83,91,115,123] : Array (Fin 128))[r.val]?.getD 0

theorem small39 : NoAtMost i5 (PetersenPackedPin.project extra39 tgt) 3 := by
  have h : PetersenPackedPin.project extra39 tgt = (0xffffeac0 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b45_1
theorem hot39 : forcedConst extra39 tgt = false := by decide +kernel
def extra40 (r : Fin 32) : Fin 128 := (#[0,1,32,33,64,65,96,97,4,5,36,37,68,69,100,101,16,17,48,49,80,81,112,113,20,21,52,53,84,85,116,117] : Array (Fin 128))[r.val]?.getD 0

theorem small40 : NoAtMost i5 (PetersenPackedPin.project extra40 tgt) 4 := by
  have h : PetersenPackedPin.project extra40 tgt = (0xfaeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b47_0
theorem hot40 : forcedConst extra40 tgt = false := by decide +kernel
def extra41 (r : Fin 32) : Fin 128 := (#[8,9,40,41,72,73,104,105,12,13,44,45,76,77,108,109,24,25,56,57,88,89,120,121,28,29,60,61,92,93,124,125] : Array (Fin 128))[r.val]?.getD 0

theorem small41 : NoAtMost i5 (PetersenPackedPin.project extra41 tgt) 3 := by
  have h : PetersenPackedPin.project extra41 tgt = (0xffffffc8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b7_2
theorem hot41 : forcedConst extra41 tgt = false := by decide +kernel
def extra42 (r : Fin 16) : Fin 128 := (#[2,34,66,98,3,35,67,99,6,38,70,102,7,39,71,103] : Array (Fin 128))[r.val]?.getD 0

theorem small42 : NoAtMost i4 (PetersenPackedPin.project extra42 tgt) 2 := by
  have h : PetersenPackedPin.project extra42 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot42 : forcedConst extra42 tgt = false := by decide +kernel
def extra43 (r : Fin 32) : Fin 128 := (#[10,42,74,106,11,43,75,107,14,46,78,110,15,47,79,111,26,58,90,122,27,59,91,123,30,62,94,126,31,63,95,127] : Array (Fin 128))[r.val]?.getD 0

theorem small43 : NoAtMost i5 (PetersenPackedPin.project extra43 tgt) 3 := by
  have h : PetersenPackedPin.project extra43 tgt = (0xfffffff8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b3_3
theorem hot43 : forcedConst extra43 tgt = false := by decide +kernel
def extra44 (r : Fin 32) : Fin 128 := (#[0,4,64,68,32,36,96,100,1,5,65,69,33,37,97,101,8,12,72,76,40,44,104,108,9,13,73,77,41,45,105,109] : Array (Fin 128))[r.val]?.getD 0

theorem small44 : NoAtMost i5 (PetersenPackedPin.project extra44 tgt) 4 := by
  have h : PetersenPackedPin.project extra44 tgt = (0xfaeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b47_0
theorem hot44 : forcedConst extra44 tgt = false := by decide +kernel
def extra45 (r : Fin 32) : Fin 128 := (#[16,20,80,84,48,52,112,116,17,21,81,85,49,53,113,117,24,28,88,92,56,60,120,124,25,29,89,93,57,61,121,125] : Array (Fin 128))[r.val]?.getD 0

theorem small45 : NoAtMost i5 (PetersenPackedPin.project extra45 tgt) 3 := by
  have h : PetersenPackedPin.project extra45 tgt = (0xffffffc8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b7_2
theorem hot45 : forcedConst extra45 tgt = false := by decide +kernel
def extra46 (r : Fin 32) : Fin 128 := (#[18,50,82,114,19,51,83,115,22,54,86,118,23,55,87,119,26,58,90,122,27,59,91,123,30,62,94,126,31,63,95,127] : Array (Fin 128))[r.val]?.getD 0

theorem small46 : NoAtMost i5 (PetersenPackedPin.project extra46 tgt) 3 := by
  have h : PetersenPackedPin.project extra46 tgt = (0xfffffff8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b3_3
theorem hot46 : forcedConst extra46 tgt = false := by decide +kernel
def extra47 (r : Fin 32) : Fin 128 := (#[0,4,8,12,16,20,24,28,1,5,9,13,17,21,25,29,64,68,72,76,80,84,88,92,65,69,73,77,81,85,89,93] : Array (Fin 128))[r.val]?.getD 0

theorem small47 : NoAtMost i5 (PetersenPackedPin.project extra47 tgt) 4 := by
  have h : PetersenPackedPin.project extra47 tgt = (0xfaeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b47_0
theorem hot47 : forcedConst extra47 tgt = false := by decide +kernel
def extra48 (r : Fin 32) : Fin 128 := (#[32,36,40,44,48,52,56,60,33,37,41,45,49,53,57,61,96,100,104,108,112,116,120,124,97,101,105,109,113,117,121,125] : Array (Fin 128))[r.val]?.getD 0

theorem small48 : NoAtMost i5 (PetersenPackedPin.project extra48 tgt) 3 := by
  have h : PetersenPackedPin.project extra48 tgt = (0xffffffc8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b7_2
theorem hot48 : forcedConst extra48 tgt = false := by decide +kernel
def extra49 (r : Fin 16) : Fin 128 := (#[2,10,18,26,3,11,19,27,6,14,22,30,7,15,23,31] : Array (Fin 128))[r.val]?.getD 0

theorem small49 : NoAtMost i4 (PetersenPackedPin.project extra49 tgt) 2 := by
  have h : PetersenPackedPin.project extra49 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot49 : forcedConst extra49 tgt = false := by decide +kernel
def extra50 (r : Fin 32) : Fin 128 := (#[34,42,50,58,35,43,51,59,38,46,54,62,39,47,55,63,98,106,114,122,99,107,115,123,102,110,118,126,103,111,119,127] : Array (Fin 128))[r.val]?.getD 0

theorem small50 : NoAtMost i5 (PetersenPackedPin.project extra50 tgt) 3 := by
  have h : PetersenPackedPin.project extra50 tgt = (0xfffffff8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b3_3
theorem hot50 : forcedConst extra50 tgt = false := by decide +kernel
def extra51 (r : Fin 32) : Fin 128 := (#[0,1,16,17,8,9,24,25,4,5,20,21,12,13,28,29,32,33,48,49,40,41,56,57,36,37,52,53,44,45,60,61] : Array (Fin 128))[r.val]?.getD 0

theorem small51 : NoAtMost i5 (PetersenPackedPin.project extra51 tgt) 4 := by
  have h : PetersenPackedPin.project extra51 tgt = (0xfaeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b47_0
theorem hot51 : forcedConst extra51 tgt = false := by decide +kernel
def extra52 (r : Fin 32) : Fin 128 := (#[64,65,80,81,72,73,88,89,68,69,84,85,76,77,92,93,96,97,112,113,104,105,120,121,100,101,116,117,108,109,124,125] : Array (Fin 128))[r.val]?.getD 0

theorem small52 : NoAtMost i5 (PetersenPackedPin.project extra52 tgt) 3 := by
  have h : PetersenPackedPin.project extra52 tgt = (0xffffffc8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b7_2
theorem hot52 : forcedConst extra52 tgt = false := by decide +kernel
def extra53 (r : Fin 32) : Fin 128 := (#[66,74,82,90,67,75,83,91,70,78,86,94,71,79,87,95,98,106,114,122,99,107,115,123,102,110,118,126,103,111,119,127] : Array (Fin 128))[r.val]?.getD 0

theorem small53 : NoAtMost i5 (PetersenPackedPin.project extra53 tgt) 3 := by
  have h : PetersenPackedPin.project extra53 tgt = (0xfffffff8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b3_3
theorem hot53 : forcedConst extra53 tgt = false := by decide +kernel
def extra54 (r : Fin 32) : Fin 128 := (#[0,1,32,33,64,65,96,97,2,3,34,35,66,67,98,99,16,17,48,49,80,81,112,113,18,19,50,51,82,83,114,115] : Array (Fin 128))[r.val]?.getD 0

theorem small54 : NoAtMost i5 (PetersenPackedPin.project extra54 tgt) 4 := by
  have h : PetersenPackedPin.project extra54 tgt = (0xeaeaeac8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b55_0
theorem hot54 : forcedConst extra54 tgt = false := by decide +kernel
def extra55 (r : Fin 32) : Fin 128 := (#[8,10,9,11,40,42,41,43,72,74,73,75,104,106,105,107,24,26,25,27,56,58,57,59,88,90,89,91,120,122,121,123] : Array (Fin 128))[r.val]?.getD 0

theorem small55 : NoAtMost i5 (PetersenPackedPin.project extra55 tgt) 4 := by
  have h : PetersenPackedPin.project extra55 tgt = (0xfffff8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b15_1
theorem hot55 : forcedConst extra55 tgt = false := by decide +kernel
def extra56 (r : Fin 32) : Fin 128 := (#[4,20,5,21,36,52,37,53,6,22,7,23,38,54,39,55,68,84,69,85,100,116,101,117,70,86,71,87,102,118,103,119] : Array (Fin 128))[r.val]?.getD 0

theorem small56 : NoAtMost i5 (PetersenPackedPin.project extra56 tgt) 3 := by
  have h : PetersenPackedPin.project extra56 tgt = (0xffffffc8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b7_2
theorem hot56 : forcedConst extra56 tgt = false := by decide +kernel
def extra57 (r : Fin 16) : Fin 128 := (#[0,2,1,3,32,34,33,35,64,66,65,67,96,98,97,99] : Array (Fin 128))[r.val]?.getD 0

theorem small57 : NoAtMost i4 (PetersenPackedPin.project extra57 tgt) 3 := by
  have h : PetersenPackedPin.project extra57 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot57 : forcedConst extra57 tgt = false := by decide +kernel
def extra58 (r : Fin 16) : Fin 128 := (#[16,48,80,112,17,49,81,113,24,56,88,120,25,57,89,121] : Array (Fin 128))[r.val]?.getD 0

theorem small58 : NoAtMost i4 (PetersenPackedPin.project extra58 tgt) 2 := by
  have h : PetersenPackedPin.project extra58 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot58 : forcedConst extra58 tgt = false := by decide +kernel
def extra59 (r : Fin 32) : Fin 128 := (#[4,5,36,37,6,7,38,39,12,13,44,45,14,15,46,47,68,69,100,101,70,71,102,103,76,77,108,109,78,79,110,111] : Array (Fin 128))[r.val]?.getD 0

theorem small59 : NoAtMost i5 (PetersenPackedPin.project extra59 tgt) 3 := by
  have h : PetersenPackedPin.project extra59 tgt = (0xfffffff8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b3_3
theorem hot59 : forcedConst extra59 tgt = false := by decide +kernel
def extra60 (r : Fin 16) : Fin 128 := (#[20,21,22,23,28,29,30,31,84,85,86,87,92,93,94,95] : Array (Fin 128))[r.val]?.getD 0

theorem small60 : NoAtMost i4 (PetersenPackedPin.project extra60 tgt) 2 := by
  have h : PetersenPackedPin.project extra60 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot60 : forcedConst extra60 tgt = false := by decide +kernel
def extra61 (r : Fin 16) : Fin 128 := (#[0,2,1,3,16,18,17,19,8,10,9,11,24,26,25,27] : Array (Fin 128))[r.val]?.getD 0

theorem small61 : NoAtMost i4 (PetersenPackedPin.project extra61 tgt) 3 := by
  have h : PetersenPackedPin.project extra61 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot61 : forcedConst extra61 tgt = false := by decide +kernel
def extra62 (r : Fin 16) : Fin 128 := (#[32,40,48,56,33,41,49,57,96,104,112,120,97,105,113,121] : Array (Fin 128))[r.val]?.getD 0

theorem small62 : NoAtMost i4 (PetersenPackedPin.project extra62 tgt) 2 := by
  have h : PetersenPackedPin.project extra62 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot62 : forcedConst extra62 tgt = false := by decide +kernel
def extra63 (r : Fin 32) : Fin 128 := (#[4,5,20,21,6,7,22,23,12,13,28,29,14,15,30,31,68,69,84,85,70,71,86,87,76,77,92,93,78,79,94,95] : Array (Fin 128))[r.val]?.getD 0

theorem small63 : NoAtMost i5 (PetersenPackedPin.project extra63 tgt) 3 := by
  have h : PetersenPackedPin.project extra63 tgt = (0xfffffff8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b3_3
theorem hot63 : forcedConst extra63 tgt = false := by decide +kernel
def extra64 (r : Fin 16) : Fin 128 := (#[36,37,38,39,44,45,46,47,100,101,102,103,108,109,110,111] : Array (Fin 128))[r.val]?.getD 0

theorem small64 : NoAtMost i4 (PetersenPackedPin.project extra64 tgt) 2 := by
  have h : PetersenPackedPin.project extra64 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot64 : forcedConst extra64 tgt = false := by decide +kernel
def extra65 (r : Fin 32) : Fin 128 := (#[0,1,16,17,8,9,24,25,2,3,18,19,10,11,26,27,32,33,48,49,40,41,56,57,34,35,50,51,42,43,58,59] : Array (Fin 128))[r.val]?.getD 0

theorem small65 : NoAtMost i5 (PetersenPackedPin.project extra65 tgt) 4 := by
  have h : PetersenPackedPin.project extra65 tgt = (0xeaeaeac8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b55_0
theorem hot65 : forcedConst extra65 tgt = false := by decide +kernel
def extra66 (r : Fin 32) : Fin 128 := (#[64,66,65,67,80,82,81,83,72,74,73,75,88,90,89,91,96,98,97,99,112,114,113,115,104,106,105,107,120,122,121,123] : Array (Fin 128))[r.val]?.getD 0

theorem small66 : NoAtMost i5 (PetersenPackedPin.project extra66 tgt) 4 := by
  have h : PetersenPackedPin.project extra66 tgt = (0xfffff8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b15_1
theorem hot66 : forcedConst extra66 tgt = false := by decide +kernel
def extra67 (r : Fin 32) : Fin 128 := (#[4,20,5,21,36,52,37,53,6,22,7,23,38,54,39,55,12,28,13,29,44,60,45,61,14,30,15,31,46,62,47,63] : Array (Fin 128))[r.val]?.getD 0

theorem small67 : NoAtMost i5 (PetersenPackedPin.project extra67 tgt) 3 := by
  have h : PetersenPackedPin.project extra67 tgt = (0xffffffc8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b7_2
theorem hot67 : forcedConst extra67 tgt = false := by decide +kernel
def extra68 (r : Fin 32) : Fin 128 := (#[16,18,20,22,80,82,84,86,48,50,52,54,112,114,116,118,17,19,21,23,81,83,85,87,49,51,53,55,113,115,117,119] : Array (Fin 128))[r.val]?.getD 0

theorem small68 : NoAtMost i5 (PetersenPackedPin.project extra68 tgt) 4 := by
  have h : PetersenPackedPin.project extra68 tgt = (0xfffff8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b15_1
theorem hot68 : forcedConst extra68 tgt = false := by decide +kernel
def extra69 (r : Fin 32) : Fin 128 := (#[8,10,9,11,40,42,41,43,72,74,73,75,104,106,105,107,12,14,13,15,44,46,45,47,76,78,77,79,108,110,109,111] : Array (Fin 128))[r.val]?.getD 0

theorem small69 : NoAtMost i5 (PetersenPackedPin.project extra69 tgt) 4 := by
  have h : PetersenPackedPin.project extra69 tgt = (0xfffff8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b15_1
theorem hot69 : forcedConst extra69 tgt = false := by decide +kernel
def extra70 (r : Fin 32) : Fin 128 := (#[0,1,2,3,4,5,6,7,64,65,66,67,68,69,70,71,16,17,18,19,20,21,22,23,80,81,82,83,84,85,86,87] : Array (Fin 128))[r.val]?.getD 0

theorem small70 : NoAtMost i5 (PetersenPackedPin.project extra70 tgt) 4 := by
  have h : PetersenPackedPin.project extra70 tgt = (0xfaeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b47_0
theorem hot70 : forcedConst extra70 tgt = false := by decide +kernel
def extra71 (r : Fin 16) : Fin 128 := (#[32,34,36,38,33,35,37,39,96,98,100,102,97,99,101,103] : Array (Fin 128))[r.val]?.getD 0

theorem small71 : NoAtMost i4 (PetersenPackedPin.project extra71 tgt) 2 := by
  have h : PetersenPackedPin.project extra71 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot71 : forcedConst extra71 tgt = false := by decide +kernel
def extra72 (r : Fin 16) : Fin 128 := (#[8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31] : Array (Fin 128))[r.val]?.getD 0

theorem small72 : NoAtMost i4 (PetersenPackedPin.project extra72 tgt) 2 := by
  have h : PetersenPackedPin.project extra72 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot72 : forcedConst extra72 tgt = false := by decide +kernel
def extra73 (r : Fin 16) : Fin 128 := (#[40,41,44,45,56,57,60,61,104,105,108,109,120,121,124,125] : Array (Fin 128))[r.val]?.getD 0

theorem small73 : NoAtMost i4 (PetersenPackedPin.project extra73 tgt) 2 := by
  have h : PetersenPackedPin.project extra73 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot73 : forcedConst extra73 tgt = false := by decide +kernel
def extra74 (r : Fin 32) : Fin 128 := (#[0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,32,33,34,35,36,37,38,39,48,49,50,51,52,53,54,55] : Array (Fin 128))[r.val]?.getD 0

theorem small74 : NoAtMost i5 (PetersenPackedPin.project extra74 tgt) 4 := by
  have h : PetersenPackedPin.project extra74 tgt = (0xeaeaeac8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b55_0
theorem hot74 : forcedConst extra74 tgt = false := by decide +kernel
def extra75 (r : Fin 32) : Fin 128 := (#[64,66,65,67,80,82,81,83,68,70,69,71,84,86,85,87,96,98,97,99,112,114,113,115,100,102,101,103,116,118,117,119] : Array (Fin 128))[r.val]?.getD 0

theorem small75 : NoAtMost i5 (PetersenPackedPin.project extra75 tgt) 3 := by
  have h : PetersenPackedPin.project extra75 tgt = (0xffffffc8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b7_2
theorem hot75 : forcedConst extra75 tgt = false := by decide +kernel
def extra76 (r : Fin 32) : Fin 128 := (#[8,10,9,11,40,42,41,43,12,14,13,15,44,46,45,47,24,26,25,27,56,58,57,59,28,30,29,31,60,62,61,63] : Array (Fin 128))[r.val]?.getD 0

theorem small76 : NoAtMost i5 (PetersenPackedPin.project extra76 tgt) 3 := by
  have h : PetersenPackedPin.project extra76 tgt = (0xffffffc8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b7_2
theorem hot76 : forcedConst extra76 tgt = false := by decide +kernel
def extra77 (r : Fin 32) : Fin 128 := (#[72,73,74,75,76,77,78,79,88,89,90,91,92,93,94,95,104,105,106,107,108,109,110,111,120,121,122,123,124,125,126,127] : Array (Fin 128))[r.val]?.getD 0

theorem small77 : NoAtMost i5 (PetersenPackedPin.project extra77 tgt) 3 := by
  have h : PetersenPackedPin.project extra77 tgt = (0xfffffff8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b3_3
theorem hot77 : forcedConst extra77 tgt = false := by decide +kernel
def extra78 (r : Fin 32) : Fin 128 := (#[0,4,2,6,1,5,3,7,8,12,10,14,9,13,11,15,64,68,66,70,65,69,67,71,72,76,74,78,73,77,75,79] : Array (Fin 128))[r.val]?.getD 0

theorem small78 : NoAtMost i5 (PetersenPackedPin.project extra78 tgt) 4 := by
  have h : PetersenPackedPin.project extra78 tgt = (0xeaeaeac8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b55_0
theorem hot78 : forcedConst extra78 tgt = false := by decide +kernel
def extra79 (r : Fin 32) : Fin 128 := (#[32,34,36,38,40,42,44,46,33,35,37,39,41,43,45,47,96,98,100,102,104,106,108,110,97,99,101,103,105,107,109,111] : Array (Fin 128))[r.val]?.getD 0

theorem small79 : NoAtMost i5 (PetersenPackedPin.project extra79 tgt) 3 := by
  have h : PetersenPackedPin.project extra79 tgt = (0xffffffc8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b7_2
theorem hot79 : forcedConst extra79 tgt = false := by decide +kernel
def extra80 (r : Fin 32) : Fin 128 := (#[16,18,20,22,80,82,84,86,17,19,21,23,81,83,85,87,24,26,28,30,88,90,92,94,25,27,29,31,89,91,93,95] : Array (Fin 128))[r.val]?.getD 0

theorem small80 : NoAtMost i5 (PetersenPackedPin.project extra80 tgt) 3 := by
  have h : PetersenPackedPin.project extra80 tgt = (0xffffffc8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b7_2
theorem hot80 : forcedConst extra80 tgt = false := by decide +kernel
def extra81 (r : Fin 32) : Fin 128 := (#[48,50,52,54,49,51,53,55,56,58,60,62,57,59,61,63,112,114,116,118,113,115,117,119,120,122,124,126,121,123,125,127] : Array (Fin 128))[r.val]?.getD 0

theorem small81 : NoAtMost i5 (PetersenPackedPin.project extra81 tgt) 3 := by
  have h : PetersenPackedPin.project extra81 tgt = (0xfffffff8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b3_3
theorem hot81 : forcedConst extra81 tgt = false := by decide +kernel
def extra82 (r : Fin 32) : Fin 128 := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47] : Array (Fin 128))[r.val]?.getD 0

theorem small82 : NoAtMost i5 (PetersenPackedPin.project extra82 tgt) 4 := by
  have h : PetersenPackedPin.project extra82 tgt = (0xfaeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b47_0
theorem hot82 : forcedConst extra82 tgt = false := by decide +kernel
def extra83 (r : Fin 16) : Fin 128 := (#[64,65,66,67,68,69,70,71,96,97,98,99,100,101,102,103] : Array (Fin 128))[r.val]?.getD 0

theorem small83 : NoAtMost i4 (PetersenPackedPin.project extra83 tgt) 2 := by
  have h : PetersenPackedPin.project extra83 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot83 : forcedConst extra83 tgt = false := by decide +kernel
def extra84 (r : Fin 16) : Fin 128 := (#[16,18,20,22,17,19,21,23,24,26,28,30,25,27,29,31] : Array (Fin 128))[r.val]?.getD 0

theorem small84 : NoAtMost i4 (PetersenPackedPin.project extra84 tgt) 2 := by
  have h : PetersenPackedPin.project extra84 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot84 : forcedConst extra84 tgt = false := by decide +kernel
def extra85 (r : Fin 16) : Fin 128 := (#[80,81,84,85,88,89,92,93,112,113,116,117,120,121,124,125] : Array (Fin 128))[r.val]?.getD 0

theorem small85 : NoAtMost i4 (PetersenPackedPin.project extra85 tgt) 2 := by
  have h : PetersenPackedPin.project extra85 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot85 : forcedConst extra85 tgt = false := by decide +kernel
def extra86 (r : Fin 32) : Fin 128 := (#[64,66,65,67,80,82,81,83,72,74,73,75,88,90,89,91,68,70,69,71,84,86,85,87,76,78,77,79,92,94,93,95] : Array (Fin 128))[r.val]?.getD 0

theorem small86 : NoAtMost i5 (PetersenPackedPin.project extra86 tgt) 4 := by
  have h : PetersenPackedPin.project extra86 tgt = (0xfffff8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b15_1
theorem hot86 : forcedConst extra86 tgt = false := by decide +kernel
def extra87 (r : Fin 32) : Fin 128 := (#[32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,33,35,37,39,41,43,45,47,49,51,53,55,57,59,61,63] : Array (Fin 128))[r.val]?.getD 0

theorem small87 : NoAtMost i5 (PetersenPackedPin.project extra87 tgt) 4 := by
  have h : PetersenPackedPin.project extra87 tgt = (0xfffff8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra191.b15_1
theorem hot87 : forcedConst extra87 tgt = false := by decide +kernel
def extra88 (r : Fin 4) : Fin 128 := (#[4,12,68,76] : Array (Fin 128))[r.val]?.getD 0
def i2 : List (BitVec 4) := [0xa,0xc]
theorem small88 : NoAtMost i2 (PetersenPackedPin.project extra88 tgt) 0 := by
  have h : PetersenPackedPin.project extra88 tgt = (0xe : BitVec 4) := by decide +kernel
  rw [h]; exact Extra191.b0_2
theorem hot88 : forcedConst extra88 tgt = false := by decide +kernel
def extra89 (r : Fin 16) : Fin 128 := (#[2,10,34,42,66,74,98,106,18,26,50,58,82,90,114,122] : Array (Fin 128))[r.val]?.getD 0

theorem small89 : NoAtMost i4 (PetersenPackedPin.project extra89 tgt) 2 := by
  have h : PetersenPackedPin.project extra89 tgt = (0xeac0 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b45_0
theorem hot89 : forcedConst extra89 tgt = false := by decide +kernel
def extra90 (r : Fin 4) : Fin 128 := (#[1,17,33,49] : Array (Fin 128))[r.val]?.getD 0

theorem small90 : NoAtMost i2 (PetersenPackedPin.project extra90 tgt) 0 := by
  have h : PetersenPackedPin.project extra90 tgt = (0xe : BitVec 4) := by decide +kernel
  rw [h]; exact Extra191.b0_2
theorem hot90 : forcedConst extra90 tgt = false := by decide +kernel
def extra91 (r : Fin 16) : Fin 128 := (#[5,13,21,29,37,45,53,61,69,77,85,93,101,109,117,125] : Array (Fin 128))[r.val]?.getD 0

theorem small91 : NoAtMost i4 (PetersenPackedPin.project extra91 tgt) 2 := by
  have h : PetersenPackedPin.project extra91 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot91 : forcedConst extra91 tgt = false := by decide +kernel
def extra92 (r : Fin 8) : Fin 128 := (#[0,4,64,68,32,36,96,100] : Array (Fin 128))[r.val]?.getD 0

theorem small92 : NoAtMost i3 (PetersenPackedPin.project extra92 tgt) 1 := by
  have h : PetersenPackedPin.project extra92 tgt = (0xc8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b7_0
theorem hot92 : forcedConst extra92 tgt = false := by decide +kernel
def extra93 (r : Fin 8) : Fin 128 := (#[2,34,66,98,6,38,70,102] : Array (Fin 128))[r.val]?.getD 0

theorem small93 : NoAtMost i3 (PetersenPackedPin.project extra93 tgt) 1 := by
  have h : PetersenPackedPin.project extra93 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot93 : forcedConst extra93 tgt = false := by decide +kernel
def extra94 (r : Fin 16) : Fin 128 := (#[10,42,74,106,14,46,78,110,26,58,90,122,30,62,94,126] : Array (Fin 128))[r.val]?.getD 0

theorem small94 : NoAtMost i4 (PetersenPackedPin.project extra94 tgt) 2 := by
  have h : PetersenPackedPin.project extra94 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot94 : forcedConst extra94 tgt = false := by decide +kernel
def extra95 (r : Fin 16) : Fin 128 := (#[1,5,65,69,17,21,81,85,33,37,97,101,49,53,113,117] : Array (Fin 128))[r.val]?.getD 0

theorem small95 : NoAtMost i4 (PetersenPackedPin.project extra95 tgt) 2 := by
  have h : PetersenPackedPin.project extra95 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot95 : forcedConst extra95 tgt = false := by decide +kernel
def extra96 (r : Fin 8) : Fin 128 := (#[9,13,25,29,41,45,57,61] : Array (Fin 128))[r.val]?.getD 0

theorem small96 : NoAtMost i3 (PetersenPackedPin.project extra96 tgt) 1 := by
  have h : PetersenPackedPin.project extra96 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot96 : forcedConst extra96 tgt = false := by decide +kernel
def extra97 (r : Fin 16) : Fin 128 := (#[0,8,4,12,64,72,68,76,32,40,36,44,96,104,100,108] : Array (Fin 128))[r.val]?.getD 0

theorem small97 : NoAtMost i4 (PetersenPackedPin.project extra97 tgt) 3 := by
  have h : PetersenPackedPin.project extra97 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot97 : forcedConst extra97 tgt = false := by decide +kernel
def extra98 (r : Fin 16) : Fin 128 := (#[16,20,80,84,48,52,112,116,24,28,88,92,56,60,120,124] : Array (Fin 128))[r.val]?.getD 0

theorem small98 : NoAtMost i4 (PetersenPackedPin.project extra98 tgt) 2 := by
  have h : PetersenPackedPin.project extra98 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot98 : forcedConst extra98 tgt = false := by decide +kernel
def extra99 (r : Fin 16) : Fin 128 := (#[18,50,82,114,22,54,86,118,26,58,90,122,30,62,94,126] : Array (Fin 128))[r.val]?.getD 0

theorem small99 : NoAtMost i4 (PetersenPackedPin.project extra99 tgt) 2 := by
  have h : PetersenPackedPin.project extra99 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot99 : forcedConst extra99 tgt = false := by decide +kernel
def extra100 (r : Fin 16) : Fin 128 := (#[1,9,5,13,65,73,69,77,33,41,37,45,97,105,101,109] : Array (Fin 128))[r.val]?.getD 0

theorem small100 : NoAtMost i4 (PetersenPackedPin.project extra100 tgt) 2 := by
  have h : PetersenPackedPin.project extra100 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot100 : forcedConst extra100 tgt = false := by decide +kernel
def extra101 (r : Fin 16) : Fin 128 := (#[0,16,8,24,4,20,12,28,64,80,72,88,68,84,76,92] : Array (Fin 128))[r.val]?.getD 0

theorem small101 : NoAtMost i4 (PetersenPackedPin.project extra101 tgt) 3 := by
  have h : PetersenPackedPin.project extra101 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot101 : forcedConst extra101 tgt = false := by decide +kernel
def extra102 (r : Fin 16) : Fin 128 := (#[32,36,40,44,48,52,56,60,96,100,104,108,112,116,120,124] : Array (Fin 128))[r.val]?.getD 0

theorem small102 : NoAtMost i4 (PetersenPackedPin.project extra102 tgt) 2 := by
  have h : PetersenPackedPin.project extra102 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot102 : forcedConst extra102 tgt = false := by decide +kernel
def extra103 (r : Fin 8) : Fin 128 := (#[2,10,18,26,6,14,22,30] : Array (Fin 128))[r.val]?.getD 0

theorem small103 : NoAtMost i3 (PetersenPackedPin.project extra103 tgt) 1 := by
  have h : PetersenPackedPin.project extra103 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot103 : forcedConst extra103 tgt = false := by decide +kernel
def extra104 (r : Fin 16) : Fin 128 := (#[34,42,50,58,38,46,54,62,98,106,114,122,102,110,118,126] : Array (Fin 128))[r.val]?.getD 0

theorem small104 : NoAtMost i4 (PetersenPackedPin.project extra104 tgt) 2 := by
  have h : PetersenPackedPin.project extra104 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot104 : forcedConst extra104 tgt = false := by decide +kernel
def extra105 (r : Fin 16) : Fin 128 := (#[1,9,5,13,65,73,69,77,17,25,21,29,81,89,85,93] : Array (Fin 128))[r.val]?.getD 0

theorem small105 : NoAtMost i4 (PetersenPackedPin.project extra105 tgt) 2 := by
  have h : PetersenPackedPin.project extra105 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot105 : forcedConst extra105 tgt = false := by decide +kernel
def extra106 (r : Fin 8) : Fin 128 := (#[0,4,8,12,16,20,24,28] : Array (Fin 128))[r.val]?.getD 0

theorem small106 : NoAtMost i3 (PetersenPackedPin.project extra106 tgt) 1 := by
  have h : PetersenPackedPin.project extra106 tgt = (0xc8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b7_0
theorem hot106 : forcedConst extra106 tgt = false := by decide +kernel
def extra107 (r : Fin 16) : Fin 128 := (#[66,74,82,90,70,78,86,94,98,106,114,122,102,110,118,126] : Array (Fin 128))[r.val]?.getD 0

theorem small107 : NoAtMost i4 (PetersenPackedPin.project extra107 tgt) 2 := by
  have h : PetersenPackedPin.project extra107 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot107 : forcedConst extra107 tgt = false := by decide +kernel
def extra108 (r : Fin 16) : Fin 128 := (#[1,5,9,13,17,21,25,29,33,37,41,45,49,53,57,61] : Array (Fin 128))[r.val]?.getD 0

theorem small108 : NoAtMost i4 (PetersenPackedPin.project extra108 tgt) 2 := by
  have h : PetersenPackedPin.project extra108 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot108 : forcedConst extra108 tgt = false := by decide +kernel
def extra109 (r : Fin 8) : Fin 128 := (#[65,69,81,85,97,101,113,117] : Array (Fin 128))[r.val]?.getD 0

theorem small109 : NoAtMost i3 (PetersenPackedPin.project extra109 tgt) 1 := by
  have h : PetersenPackedPin.project extra109 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot109 : forcedConst extra109 tgt = false := by decide +kernel
def extra110 (r : Fin 4) : Fin 128 := (#[0,32,64,96] : Array (Fin 128))[r.val]?.getD 0

theorem small110 : NoAtMost i2 (PetersenPackedPin.project extra110 tgt) 0 := by
  have h : PetersenPackedPin.project extra110 tgt = (0x8 : BitVec 4) := by decide +kernel
  rw [h]; exact Extra191.b3_0
theorem hot110 : forcedConst extra110 tgt = false := by decide +kernel
def extra111 (r : Fin 8) : Fin 128 := (#[8,40,72,104,24,56,88,120] : Array (Fin 128))[r.val]?.getD 0

theorem small111 : NoAtMost i3 (PetersenPackedPin.project extra111 tgt) 1 := by
  have h : PetersenPackedPin.project extra111 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot111 : forcedConst extra111 tgt = false := by decide +kernel
def extra112 (r : Fin 4) : Fin 128 := (#[4,6,68,70] : Array (Fin 128))[r.val]?.getD 0

theorem small112 : NoAtMost i2 (PetersenPackedPin.project extra112 tgt) 0 := by
  have h : PetersenPackedPin.project extra112 tgt = (0xe : BitVec 4) := by decide +kernel
  rw [h]; exact Extra191.b0_2
theorem hot112 : forcedConst extra112 tgt = false := by decide +kernel
def extra113 (r : Fin 8) : Fin 128 := (#[9,11,25,27,41,43,57,59] : Array (Fin 128))[r.val]?.getD 0

theorem small113 : NoAtMost i3 (PetersenPackedPin.project extra113 tgt) 1 := by
  have h : PetersenPackedPin.project extra113 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot113 : forcedConst extra113 tgt = false := by decide +kernel
def extra114 (r : Fin 16) : Fin 128 := (#[5,7,21,23,37,39,53,55,69,71,85,87,101,103,117,119] : Array (Fin 128))[r.val]?.getD 0

theorem small114 : NoAtMost i4 (PetersenPackedPin.project extra114 tgt) 2 := by
  have h : PetersenPackedPin.project extra114 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot114 : forcedConst extra114 tgt = false := by decide +kernel
def extra115 (r : Fin 8) : Fin 128 := (#[16,48,80,112,24,56,88,120] : Array (Fin 128))[r.val]?.getD 0

theorem small115 : NoAtMost i3 (PetersenPackedPin.project extra115 tgt) 1 := by
  have h : PetersenPackedPin.project extra115 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot115 : forcedConst extra115 tgt = false := by decide +kernel
def extra116 (r : Fin 8) : Fin 128 := (#[20,22,28,30,84,86,92,94] : Array (Fin 128))[r.val]?.getD 0

theorem small116 : NoAtMost i3 (PetersenPackedPin.project extra116 tgt) 1 := by
  have h : PetersenPackedPin.project extra116 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot116 : forcedConst extra116 tgt = false := by decide +kernel
def extra117 (r : Fin 4) : Fin 128 := (#[1,3,33,35] : Array (Fin 128))[r.val]?.getD 0

theorem small117 : NoAtMost i2 (PetersenPackedPin.project extra117 tgt) 0 := by
  have h : PetersenPackedPin.project extra117 tgt = (0xe : BitVec 4) := by decide +kernel
  rw [h]; exact Extra191.b0_2
theorem hot117 : forcedConst extra117 tgt = false := by decide +kernel
def extra118 (r : Fin 16) : Fin 128 := (#[5,7,13,15,37,39,45,47,69,71,77,79,101,103,109,111] : Array (Fin 128))[r.val]?.getD 0

theorem small118 : NoAtMost i4 (PetersenPackedPin.project extra118 tgt) 2 := by
  have h : PetersenPackedPin.project extra118 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot118 : forcedConst extra118 tgt = false := by decide +kernel
def extra119 (r : Fin 4) : Fin 128 := (#[0,8,16,24] : Array (Fin 128))[r.val]?.getD 0

theorem small119 : NoAtMost i2 (PetersenPackedPin.project extra119 tgt) 0 := by
  have h : PetersenPackedPin.project extra119 tgt = (0x8 : BitVec 4) := by decide +kernel
  rw [h]; exact Extra191.b3_0
theorem hot119 : forcedConst extra119 tgt = false := by decide +kernel
def extra120 (r : Fin 8) : Fin 128 := (#[32,40,48,56,96,104,112,120] : Array (Fin 128))[r.val]?.getD 0

theorem small120 : NoAtMost i3 (PetersenPackedPin.project extra120 tgt) 1 := by
  have h : PetersenPackedPin.project extra120 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot120 : forcedConst extra120 tgt = false := by decide +kernel
def extra121 (r : Fin 8) : Fin 128 := (#[36,38,44,46,100,102,108,110] : Array (Fin 128))[r.val]?.getD 0

theorem small121 : NoAtMost i3 (PetersenPackedPin.project extra121 tgt) 1 := by
  have h : PetersenPackedPin.project extra121 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot121 : forcedConst extra121 tgt = false := by decide +kernel
def extra122 (r : Fin 4) : Fin 128 := (#[1,3,17,19] : Array (Fin 128))[r.val]?.getD 0

theorem small122 : NoAtMost i2 (PetersenPackedPin.project extra122 tgt) 0 := by
  have h : PetersenPackedPin.project extra122 tgt = (0xe : BitVec 4) := by decide +kernel
  rw [h]; exact Extra191.b0_2
theorem hot122 : forcedConst extra122 tgt = false := by decide +kernel
def extra123 (r : Fin 16) : Fin 128 := (#[5,7,13,15,21,23,29,31,69,71,77,79,85,87,93,95] : Array (Fin 128))[r.val]?.getD 0

theorem small123 : NoAtMost i4 (PetersenPackedPin.project extra123 tgt) 2 := by
  have h : PetersenPackedPin.project extra123 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot123 : forcedConst extra123 tgt = false := by decide +kernel
def extra124 (r : Fin 8) : Fin 128 := (#[64,72,80,88,96,104,112,120] : Array (Fin 128))[r.val]?.getD 0

theorem small124 : NoAtMost i3 (PetersenPackedPin.project extra124 tgt) 1 := by
  have h : PetersenPackedPin.project extra124 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot124 : forcedConst extra124 tgt = false := by decide +kernel
def extra125 (r : Fin 4) : Fin 128 := (#[4,6,12,14] : Array (Fin 128))[r.val]?.getD 0

theorem small125 : NoAtMost i2 (PetersenPackedPin.project extra125 tgt) 0 := by
  have h : PetersenPackedPin.project extra125 tgt = (0xe : BitVec 4) := by decide +kernel
  rw [h]; exact Extra191.b0_2
theorem hot125 : forcedConst extra125 tgt = false := by decide +kernel
def extra126 (r : Fin 8) : Fin 128 := (#[65,67,81,83,97,99,113,115] : Array (Fin 128))[r.val]?.getD 0

theorem small126 : NoAtMost i3 (PetersenPackedPin.project extra126 tgt) 1 := by
  have h : PetersenPackedPin.project extra126 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot126 : forcedConst extra126 tgt = false := by decide +kernel
def extra127 (r : Fin 16) : Fin 128 := (#[5,7,13,15,21,23,29,31,37,39,45,47,53,55,61,63] : Array (Fin 128))[r.val]?.getD 0

theorem small127 : NoAtMost i4 (PetersenPackedPin.project extra127 tgt) 2 := by
  have h : PetersenPackedPin.project extra127 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot127 : forcedConst extra127 tgt = false := by decide +kernel
def extra128 (r : Fin 16) : Fin 128 := (#[16,18,20,22,80,82,84,86,48,50,52,54,112,114,116,118] : Array (Fin 128))[r.val]?.getD 0

theorem small128 : NoAtMost i4 (PetersenPackedPin.project extra128 tgt) 3 := by
  have h : PetersenPackedPin.project extra128 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot128 : forcedConst extra128 tgt = false := by decide +kernel
def extra129 (r : Fin 8) : Fin 128 := (#[8,40,72,104,12,44,76,108] : Array (Fin 128))[r.val]?.getD 0

theorem small129 : NoAtMost i3 (PetersenPackedPin.project extra129 tgt) 1 := by
  have h : PetersenPackedPin.project extra129 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot129 : forcedConst extra129 tgt = false := by decide +kernel
def extra130 (r : Fin 16) : Fin 128 := (#[1,5,65,69,3,7,67,71,33,37,97,101,35,39,99,103] : Array (Fin 128))[r.val]?.getD 0

theorem small130 : NoAtMost i4 (PetersenPackedPin.project extra130 tgt) 2 := by
  have h : PetersenPackedPin.project extra130 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot130 : forcedConst extra130 tgt = false := by decide +kernel
def extra131 (r : Fin 8) : Fin 128 := (#[9,11,13,15,41,43,45,47] : Array (Fin 128))[r.val]?.getD 0

theorem small131 : NoAtMost i3 (PetersenPackedPin.project extra131 tgt) 1 := by
  have h : PetersenPackedPin.project extra131 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot131 : forcedConst extra131 tgt = false := by decide +kernel
def extra132 (r : Fin 8) : Fin 128 := (#[0,2,4,6,64,66,68,70] : Array (Fin 128))[r.val]?.getD 0

theorem small132 : NoAtMost i3 (PetersenPackedPin.project extra132 tgt) 1 := by
  have h : PetersenPackedPin.project extra132 tgt = (0xc8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b7_0
theorem hot132 : forcedConst extra132 tgt = false := by decide +kernel
def extra133 (r : Fin 8) : Fin 128 := (#[32,34,36,38,96,98,100,102] : Array (Fin 128))[r.val]?.getD 0

theorem small133 : NoAtMost i3 (PetersenPackedPin.project extra133 tgt) 1 := by
  have h : PetersenPackedPin.project extra133 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot133 : forcedConst extra133 tgt = false := by decide +kernel
def extra134 (r : Fin 4) : Fin 128 := (#[8,12,24,28] : Array (Fin 128))[r.val]?.getD 0

theorem small134 : NoAtMost i2 (PetersenPackedPin.project extra134 tgt) 0 := by
  have h : PetersenPackedPin.project extra134 tgt = (0xe : BitVec 4) := by decide +kernel
  rw [h]; exact Extra191.b0_2
theorem hot134 : forcedConst extra134 tgt = false := by decide +kernel
def extra135 (r : Fin 8) : Fin 128 := (#[40,44,56,60,104,108,120,124] : Array (Fin 128))[r.val]?.getD 0

theorem small135 : NoAtMost i3 (PetersenPackedPin.project extra135 tgt) 1 := by
  have h : PetersenPackedPin.project extra135 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot135 : forcedConst extra135 tgt = false := by decide +kernel
def extra136 (r : Fin 16) : Fin 128 := (#[1,5,65,69,3,7,67,71,17,21,81,85,19,23,83,87] : Array (Fin 128))[r.val]?.getD 0

theorem small136 : NoAtMost i4 (PetersenPackedPin.project extra136 tgt) 2 := by
  have h : PetersenPackedPin.project extra136 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot136 : forcedConst extra136 tgt = false := by decide +kernel
def extra137 (r : Fin 8) : Fin 128 := (#[9,11,13,15,25,27,29,31] : Array (Fin 128))[r.val]?.getD 0

theorem small137 : NoAtMost i3 (PetersenPackedPin.project extra137 tgt) 1 := by
  have h : PetersenPackedPin.project extra137 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot137 : forcedConst extra137 tgt = false := by decide +kernel
def extra138 (r : Fin 4) : Fin 128 := (#[0,2,4,6] : Array (Fin 128))[r.val]?.getD 0

theorem small138 : NoAtMost i2 (PetersenPackedPin.project extra138 tgt) 0 := by
  have h : PetersenPackedPin.project extra138 tgt = (0x8 : BitVec 4) := by decide +kernel
  rw [h]; exact Extra191.b3_0
theorem hot138 : forcedConst extra138 tgt = false := by decide +kernel
def extra139 (r : Fin 4) : Fin 128 := (#[64,68,96,100] : Array (Fin 128))[r.val]?.getD 0

theorem small139 : NoAtMost i2 (PetersenPackedPin.project extra139 tgt) 0 := by
  have h : PetersenPackedPin.project extra139 tgt = (0xe : BitVec 4) := by decide +kernel
  rw [h]; exact Extra191.b0_2
theorem hot139 : forcedConst extra139 tgt = false := by decide +kernel
def extra140 (r : Fin 8) : Fin 128 := (#[72,76,88,92,104,108,120,124] : Array (Fin 128))[r.val]?.getD 0

theorem small140 : NoAtMost i3 (PetersenPackedPin.project extra140 tgt) 1 := by
  have h : PetersenPackedPin.project extra140 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot140 : forcedConst extra140 tgt = false := by decide +kernel
def extra141 (r : Fin 16) : Fin 128 := (#[73,75,77,79,89,91,93,95,105,107,109,111,121,123,125,127] : Array (Fin 128))[r.val]?.getD 0

theorem small141 : NoAtMost i4 (PetersenPackedPin.project extra141 tgt) 2 := by
  have h : PetersenPackedPin.project extra141 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot141 : forcedConst extra141 tgt = false := by decide +kernel
def extra142 (r : Fin 16) : Fin 128 := (#[0,4,2,6,8,12,10,14,64,68,66,70,72,76,74,78] : Array (Fin 128))[r.val]?.getD 0

theorem small142 : NoAtMost i4 (PetersenPackedPin.project extra142 tgt) 2 := by
  have h : PetersenPackedPin.project extra142 tgt = (0xaaa8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b51_0
theorem hot142 : forcedConst extra142 tgt = false := by decide +kernel
def extra143 (r : Fin 16) : Fin 128 := (#[32,34,36,38,40,42,44,46,96,98,100,102,104,106,108,110] : Array (Fin 128))[r.val]?.getD 0

theorem small143 : NoAtMost i4 (PetersenPackedPin.project extra143 tgt) 2 := by
  have h : PetersenPackedPin.project extra143 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot143 : forcedConst extra143 tgt = false := by decide +kernel
def extra144 (r : Fin 16) : Fin 128 := (#[16,18,20,22,80,82,84,86,24,26,28,30,88,90,92,94] : Array (Fin 128))[r.val]?.getD 0

theorem small144 : NoAtMost i4 (PetersenPackedPin.project extra144 tgt) 2 := by
  have h : PetersenPackedPin.project extra144 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot144 : forcedConst extra144 tgt = false := by decide +kernel
def extra145 (r : Fin 16) : Fin 128 := (#[48,50,52,54,56,58,60,62,112,114,116,118,120,122,124,126] : Array (Fin 128))[r.val]?.getD 0

theorem small145 : NoAtMost i4 (PetersenPackedPin.project extra145 tgt) 2 := by
  have h : PetersenPackedPin.project extra145 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot145 : forcedConst extra145 tgt = false := by decide +kernel
def extra146 (r : Fin 16) : Fin 128 := (#[1,9,5,13,65,73,69,77,3,11,7,15,67,75,71,79] : Array (Fin 128))[r.val]?.getD 0

theorem small146 : NoAtMost i4 (PetersenPackedPin.project extra146 tgt) 2 := by
  have h : PetersenPackedPin.project extra146 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot146 : forcedConst extra146 tgt = false := by decide +kernel
def extra147 (r : Fin 8) : Fin 128 := (#[0,2,4,6,8,10,12,14] : Array (Fin 128))[r.val]?.getD 0

theorem small147 : NoAtMost i3 (PetersenPackedPin.project extra147 tgt) 1 := by
  have h : PetersenPackedPin.project extra147 tgt = (0xc8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b7_0
theorem hot147 : forcedConst extra147 tgt = false := by decide +kernel
def extra148 (r : Fin 8) : Fin 128 := (#[16,18,20,22,24,26,28,30] : Array (Fin 128))[r.val]?.getD 0

theorem small148 : NoAtMost i3 (PetersenPackedPin.project extra148 tgt) 1 := by
  have h : PetersenPackedPin.project extra148 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot148 : forcedConst extra148 tgt = false := by decide +kernel
def extra149 (r : Fin 8) : Fin 128 := (#[80,84,88,92,112,116,120,124] : Array (Fin 128))[r.val]?.getD 0

theorem small149 : NoAtMost i3 (PetersenPackedPin.project extra149 tgt) 1 := by
  have h : PetersenPackedPin.project extra149 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot149 : forcedConst extra149 tgt = false := by decide +kernel
def extra150 (r : Fin 16) : Fin 128 := (#[1,5,9,13,3,7,11,15,33,37,41,45,35,39,43,47] : Array (Fin 128))[r.val]?.getD 0

theorem small150 : NoAtMost i4 (PetersenPackedPin.project extra150 tgt) 2 := by
  have h : PetersenPackedPin.project extra150 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot150 : forcedConst extra150 tgt = false := by decide +kernel
def extra151 (r : Fin 8) : Fin 128 := (#[65,67,69,71,97,99,101,103] : Array (Fin 128))[r.val]?.getD 0

theorem small151 : NoAtMost i3 (PetersenPackedPin.project extra151 tgt) 1 := by
  have h : PetersenPackedPin.project extra151 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot151 : forcedConst extra151 tgt = false := by decide +kernel
def extra152 (r : Fin 8) : Fin 128 := (#[64,72,80,88,68,76,84,92] : Array (Fin 128))[r.val]?.getD 0

theorem small152 : NoAtMost i3 (PetersenPackedPin.project extra152 tgt) 1 := by
  have h : PetersenPackedPin.project extra152 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot152 : forcedConst extra152 tgt = false := by decide +kernel
def extra153 (r : Fin 16) : Fin 128 := (#[32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62] : Array (Fin 128))[r.val]?.getD 0

theorem small153 : NoAtMost i4 (PetersenPackedPin.project extra153 tgt) 3 := by
  have h : PetersenPackedPin.project extra153 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot153 : forcedConst extra153 tgt = false := by decide +kernel
def extra154 (r : Fin 16) : Fin 128 := (#[1,5,9,13,3,7,11,15,17,21,25,29,19,23,27,31] : Array (Fin 128))[r.val]?.getD 0

theorem small154 : NoAtMost i4 (PetersenPackedPin.project extra154 tgt) 2 := by
  have h : PetersenPackedPin.project extra154 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot154 : forcedConst extra154 tgt = false := by decide +kernel
def extra155 (r : Fin 8) : Fin 128 := (#[65,67,69,71,81,83,85,87] : Array (Fin 128))[r.val]?.getD 0

theorem small155 : NoAtMost i3 (PetersenPackedPin.project extra155 tgt) 1 := by
  have h : PetersenPackedPin.project extra155 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot155 : forcedConst extra155 tgt = false := by decide +kernel
def extra156 (r : Fin 16) : Fin 128 := (#[0,16,1,17,32,48,33,49,64,80,65,81,96,112,97,113] : Array (Fin 128))[r.val]?.getD 0

theorem small156 : NoAtMost i4 (PetersenPackedPin.project extra156 tgt) 3 := by
  have h : PetersenPackedPin.project extra156 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot156 : forcedConst extra156 tgt = false := by decide +kernel
def extra157 (r : Fin 16) : Fin 128 := (#[8,9,40,41,72,73,104,105,24,25,56,57,88,89,120,121] : Array (Fin 128))[r.val]?.getD 0

theorem small157 : NoAtMost i4 (PetersenPackedPin.project extra157 tgt) 2 := by
  have h : PetersenPackedPin.project extra157 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot157 : forcedConst extra157 tgt = false := by decide +kernel
def extra158 (r : Fin 16) : Fin 128 := (#[4,20,5,21,36,52,37,53,68,84,69,85,100,116,101,117] : Array (Fin 128))[r.val]?.getD 0

theorem small158 : NoAtMost i4 (PetersenPackedPin.project extra158 tgt) 2 := by
  have h : PetersenPackedPin.project extra158 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot158 : forcedConst extra158 tgt = false := by decide +kernel
def extra159 (r : Fin 8) : Fin 128 := (#[2,34,66,98,3,35,67,99] : Array (Fin 128))[r.val]?.getD 0

theorem small159 : NoAtMost i3 (PetersenPackedPin.project extra159 tgt) 1 := by
  have h : PetersenPackedPin.project extra159 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot159 : forcedConst extra159 tgt = false := by decide +kernel
def extra160 (r : Fin 16) : Fin 128 := (#[10,42,74,106,11,43,75,107,26,58,90,122,27,59,91,123] : Array (Fin 128))[r.val]?.getD 0

theorem small160 : NoAtMost i4 (PetersenPackedPin.project extra160 tgt) 2 := by
  have h : PetersenPackedPin.project extra160 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot160 : forcedConst extra160 tgt = false := by decide +kernel
def extra161 (r : Fin 8) : Fin 128 := (#[0,1,32,33,64,65,96,97] : Array (Fin 128))[r.val]?.getD 0

theorem small161 : NoAtMost i3 (PetersenPackedPin.project extra161 tgt) 1 := by
  have h : PetersenPackedPin.project extra161 tgt = (0xc8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b7_0
theorem hot161 : forcedConst extra161 tgt = false := by decide +kernel
def extra162 (r : Fin 16) : Fin 128 := (#[4,5,36,37,12,13,44,45,68,69,100,101,76,77,108,109] : Array (Fin 128))[r.val]?.getD 0

theorem small162 : NoAtMost i4 (PetersenPackedPin.project extra162 tgt) 2 := by
  have h : PetersenPackedPin.project extra162 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot162 : forcedConst extra162 tgt = false := by decide +kernel
def extra163 (r : Fin 8) : Fin 128 := (#[20,21,28,29,84,85,92,93] : Array (Fin 128))[r.val]?.getD 0

theorem small163 : NoAtMost i3 (PetersenPackedPin.project extra163 tgt) 1 := by
  have h : PetersenPackedPin.project extra163 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot163 : forcedConst extra163 tgt = false := by decide +kernel
def extra164 (r : Fin 16) : Fin 128 := (#[18,50,82,114,19,51,83,115,26,58,90,122,27,59,91,123] : Array (Fin 128))[r.val]?.getD 0

theorem small164 : NoAtMost i4 (PetersenPackedPin.project extra164 tgt) 2 := by
  have h : PetersenPackedPin.project extra164 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot164 : forcedConst extra164 tgt = false := by decide +kernel
def extra165 (r : Fin 8) : Fin 128 := (#[0,1,16,17,8,9,24,25] : Array (Fin 128))[r.val]?.getD 0

theorem small165 : NoAtMost i3 (PetersenPackedPin.project extra165 tgt) 1 := by
  have h : PetersenPackedPin.project extra165 tgt = (0xc8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b7_0
theorem hot165 : forcedConst extra165 tgt = false := by decide +kernel
def extra166 (r : Fin 16) : Fin 128 := (#[4,5,20,21,12,13,28,29,68,69,84,85,76,77,92,93] : Array (Fin 128))[r.val]?.getD 0

theorem small166 : NoAtMost i4 (PetersenPackedPin.project extra166 tgt) 2 := by
  have h : PetersenPackedPin.project extra166 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot166 : forcedConst extra166 tgt = false := by decide +kernel
def extra167 (r : Fin 8) : Fin 128 := (#[36,37,44,45,100,101,108,109] : Array (Fin 128))[r.val]?.getD 0

theorem small167 : NoAtMost i3 (PetersenPackedPin.project extra167 tgt) 1 := by
  have h : PetersenPackedPin.project extra167 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot167 : forcedConst extra167 tgt = false := by decide +kernel
def extra168 (r : Fin 8) : Fin 128 := (#[2,10,18,26,3,11,19,27] : Array (Fin 128))[r.val]?.getD 0

theorem small168 : NoAtMost i3 (PetersenPackedPin.project extra168 tgt) 1 := by
  have h : PetersenPackedPin.project extra168 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot168 : forcedConst extra168 tgt = false := by decide +kernel
def extra169 (r : Fin 16) : Fin 128 := (#[34,42,50,58,35,43,51,59,98,106,114,122,99,107,115,123] : Array (Fin 128))[r.val]?.getD 0

theorem small169 : NoAtMost i4 (PetersenPackedPin.project extra169 tgt) 2 := by
  have h : PetersenPackedPin.project extra169 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot169 : forcedConst extra169 tgt = false := by decide +kernel
def extra170 (r : Fin 16) : Fin 128 := (#[0,8,16,24,1,9,17,25,32,40,48,56,33,41,49,57] : Array (Fin 128))[r.val]?.getD 0

theorem small170 : NoAtMost i4 (PetersenPackedPin.project extra170 tgt) 3 := by
  have h : PetersenPackedPin.project extra170 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot170 : forcedConst extra170 tgt = false := by decide +kernel
def extra171 (r : Fin 16) : Fin 128 := (#[64,65,80,81,72,73,88,89,96,97,112,113,104,105,120,121] : Array (Fin 128))[r.val]?.getD 0

theorem small171 : NoAtMost i4 (PetersenPackedPin.project extra171 tgt) 2 := by
  have h : PetersenPackedPin.project extra171 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot171 : forcedConst extra171 tgt = false := by decide +kernel
def extra172 (r : Fin 16) : Fin 128 := (#[4,20,5,21,36,52,37,53,12,28,13,29,44,60,45,61] : Array (Fin 128))[r.val]?.getD 0

theorem small172 : NoAtMost i4 (PetersenPackedPin.project extra172 tgt) 2 := by
  have h : PetersenPackedPin.project extra172 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot172 : forcedConst extra172 tgt = false := by decide +kernel
def extra173 (r : Fin 16) : Fin 128 := (#[66,74,82,90,67,75,83,91,98,106,114,122,99,107,115,123] : Array (Fin 128))[r.val]?.getD 0

theorem small173 : NoAtMost i4 (PetersenPackedPin.project extra173 tgt) 2 := by
  have h : PetersenPackedPin.project extra173 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot173 : forcedConst extra173 tgt = false := by decide +kernel
def extra174 (r : Fin 16) : Fin 128 := (#[0,1,32,33,64,65,96,97,4,5,36,37,68,69,100,101] : Array (Fin 128))[r.val]?.getD 0

theorem small174 : NoAtMost i4 (PetersenPackedPin.project extra174 tgt) 3 := by
  have h : PetersenPackedPin.project extra174 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot174 : forcedConst extra174 tgt = false := by decide +kernel
def extra175 (r : Fin 16) : Fin 128 := (#[16,20,80,84,48,52,112,116,17,21,81,85,49,53,113,117] : Array (Fin 128))[r.val]?.getD 0

theorem small175 : NoAtMost i4 (PetersenPackedPin.project extra175 tgt) 2 := by
  have h : PetersenPackedPin.project extra175 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot175 : forcedConst extra175 tgt = false := by decide +kernel
def extra176 (r : Fin 16) : Fin 128 := (#[8,9,40,41,72,73,104,105,12,13,44,45,76,77,108,109] : Array (Fin 128))[r.val]?.getD 0

theorem small176 : NoAtMost i4 (PetersenPackedPin.project extra176 tgt) 2 := by
  have h : PetersenPackedPin.project extra176 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot176 : forcedConst extra176 tgt = false := by decide +kernel
def extra177 (r : Fin 16) : Fin 128 := (#[18,50,82,114,19,51,83,115,22,54,86,118,23,55,87,119] : Array (Fin 128))[r.val]?.getD 0

theorem small177 : NoAtMost i4 (PetersenPackedPin.project extra177 tgt) 2 := by
  have h : PetersenPackedPin.project extra177 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot177 : forcedConst extra177 tgt = false := by decide +kernel
def extra178 (r : Fin 16) : Fin 128 := (#[10,42,74,106,11,43,75,107,14,46,78,110,15,47,79,111] : Array (Fin 128))[r.val]?.getD 0

theorem small178 : NoAtMost i4 (PetersenPackedPin.project extra178 tgt) 2 := by
  have h : PetersenPackedPin.project extra178 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot178 : forcedConst extra178 tgt = false := by decide +kernel
def extra179 (r : Fin 16) : Fin 128 := (#[0,1,4,5,64,65,68,69,16,17,20,21,80,81,84,85] : Array (Fin 128))[r.val]?.getD 0

theorem small179 : NoAtMost i4 (PetersenPackedPin.project extra179 tgt) 2 := by
  have h : PetersenPackedPin.project extra179 tgt = (0xeac0 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b45_0
theorem hot179 : forcedConst extra179 tgt = false := by decide +kernel
def extra180 (r : Fin 4) : Fin 128 := (#[32,33,96,97] : Array (Fin 128))[r.val]?.getD 0

theorem small180 : NoAtMost i2 (PetersenPackedPin.project extra180 tgt) 0 := by
  have h : PetersenPackedPin.project extra180 tgt = (0xe : BitVec 4) := by decide +kernel
  rw [h]; exact Extra191.b0_2
theorem hot180 : forcedConst extra180 tgt = false := by decide +kernel
def extra181 (r : Fin 4) : Fin 128 := (#[2,3,6,7] : Array (Fin 128))[r.val]?.getD 0

theorem small181 : NoAtMost i2 (PetersenPackedPin.project extra181 tgt) 0 := by
  have h : PetersenPackedPin.project extra181 tgt = (0xe : BitVec 4) := by decide +kernel
  rw [h]; exact Extra191.b0_2
theorem hot181 : forcedConst extra181 tgt = false := by decide +kernel
def extra182 (r : Fin 8) : Fin 128 := (#[34,35,38,39,98,99,102,103] : Array (Fin 128))[r.val]?.getD 0

theorem small182 : NoAtMost i3 (PetersenPackedPin.project extra182 tgt) 1 := by
  have h : PetersenPackedPin.project extra182 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot182 : forcedConst extra182 tgt = false := by decide +kernel
def extra183 (r : Fin 8) : Fin 128 := (#[10,11,14,15,26,27,30,31] : Array (Fin 128))[r.val]?.getD 0

theorem small183 : NoAtMost i3 (PetersenPackedPin.project extra183 tgt) 1 := by
  have h : PetersenPackedPin.project extra183 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot183 : forcedConst extra183 tgt = false := by decide +kernel
def extra184 (r : Fin 16) : Fin 128 := (#[42,43,46,47,58,59,62,63,106,107,110,111,122,123,126,127] : Array (Fin 128))[r.val]?.getD 0

theorem small184 : NoAtMost i4 (PetersenPackedPin.project extra184 tgt) 2 := by
  have h : PetersenPackedPin.project extra184 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot184 : forcedConst extra184 tgt = false := by decide +kernel
def extra185 (r : Fin 8) : Fin 128 := (#[0,16,1,17,32,48,33,49] : Array (Fin 128))[r.val]?.getD 0

theorem small185 : NoAtMost i3 (PetersenPackedPin.project extra185 tgt) 1 := by
  have h : PetersenPackedPin.project extra185 tgt = (0xc8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b7_0
theorem hot185 : forcedConst extra185 tgt = false := by decide +kernel
def extra186 (r : Fin 16) : Fin 128 := (#[64,65,80,81,68,69,84,85,96,97,112,113,100,101,116,117] : Array (Fin 128))[r.val]?.getD 0

theorem small186 : NoAtMost i4 (PetersenPackedPin.project extra186 tgt) 2 := by
  have h : PetersenPackedPin.project extra186 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot186 : forcedConst extra186 tgt = false := by decide +kernel
def extra187 (r : Fin 16) : Fin 128 := (#[8,9,40,41,12,13,44,45,24,25,56,57,28,29,60,61] : Array (Fin 128))[r.val]?.getD 0

theorem small187 : NoAtMost i4 (PetersenPackedPin.project extra187 tgt) 2 := by
  have h : PetersenPackedPin.project extra187 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot187 : forcedConst extra187 tgt = false := by decide +kernel
def extra188 (r : Fin 8) : Fin 128 := (#[66,67,70,71,98,99,102,103] : Array (Fin 128))[r.val]?.getD 0

theorem small188 : NoAtMost i3 (PetersenPackedPin.project extra188 tgt) 1 := by
  have h : PetersenPackedPin.project extra188 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot188 : forcedConst extra188 tgt = false := by decide +kernel
def extra189 (r : Fin 16) : Fin 128 := (#[74,75,78,79,90,91,94,95,106,107,110,111,122,123,126,127] : Array (Fin 128))[r.val]?.getD 0

theorem small189 : NoAtMost i4 (PetersenPackedPin.project extra189 tgt) 2 := by
  have h : PetersenPackedPin.project extra189 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot189 : forcedConst extra189 tgt = false := by decide +kernel
def extra190 (r : Fin 8) : Fin 128 := (#[0,8,4,12,64,72,68,76] : Array (Fin 128))[r.val]?.getD 0

theorem small190 : NoAtMost i3 (PetersenPackedPin.project extra190 tgt) 1 := by
  have h : PetersenPackedPin.project extra190 tgt = (0xc8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b7_0
theorem hot190 : forcedConst extra190 tgt = false := by decide +kernel
def extra191 (r : Fin 16) : Fin 128 := (#[32,36,40,44,33,37,41,45,96,100,104,108,97,101,105,109] : Array (Fin 128))[r.val]?.getD 0

theorem small191 : NoAtMost i4 (PetersenPackedPin.project extra191 tgt) 2 := by
  have h : PetersenPackedPin.project extra191 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot191 : forcedConst extra191 tgt = false := by decide +kernel
def extra192 (r : Fin 16) : Fin 128 := (#[16,20,80,84,17,21,81,85,24,28,88,92,25,29,89,93] : Array (Fin 128))[r.val]?.getD 0

theorem small192 : NoAtMost i4 (PetersenPackedPin.project extra192 tgt) 2 := by
  have h : PetersenPackedPin.project extra192 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot192 : forcedConst extra192 tgt = false := by decide +kernel
def extra193 (r : Fin 8) : Fin 128 := (#[48,49,56,57,112,113,120,121] : Array (Fin 128))[r.val]?.getD 0

theorem small193 : NoAtMost i3 (PetersenPackedPin.project extra193 tgt) 1 := by
  have h : PetersenPackedPin.project extra193 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot193 : forcedConst extra193 tgt = false := by decide +kernel
def extra194 (r : Fin 8) : Fin 128 := (#[18,19,22,23,26,27,30,31] : Array (Fin 128))[r.val]?.getD 0

theorem small194 : NoAtMost i3 (PetersenPackedPin.project extra194 tgt) 1 := by
  have h : PetersenPackedPin.project extra194 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot194 : forcedConst extra194 tgt = false := by decide +kernel
def extra195 (r : Fin 16) : Fin 128 := (#[50,51,54,55,58,59,62,63,114,115,118,119,122,123,126,127] : Array (Fin 128))[r.val]?.getD 0

theorem small195 : NoAtMost i4 (PetersenPackedPin.project extra195 tgt) 2 := by
  have h : PetersenPackedPin.project extra195 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot195 : forcedConst extra195 tgt = false := by decide +kernel
def extra196 (r : Fin 16) : Fin 128 := (#[0,1,4,5,8,9,12,13,32,33,36,37,40,41,44,45] : Array (Fin 128))[r.val]?.getD 0

theorem small196 : NoAtMost i4 (PetersenPackedPin.project extra196 tgt) 2 := by
  have h : PetersenPackedPin.project extra196 tgt = (0xeac0 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b45_0
theorem hot196 : forcedConst extra196 tgt = false := by decide +kernel
def extra197 (r : Fin 4) : Fin 128 := (#[16,17,24,25] : Array (Fin 128))[r.val]?.getD 0

theorem small197 : NoAtMost i2 (PetersenPackedPin.project extra197 tgt) 0 := by
  have h : PetersenPackedPin.project extra197 tgt = (0xe : BitVec 4) := by decide +kernel
  rw [h]; exact Extra191.b0_2
theorem hot197 : forcedConst extra197 tgt = false := by decide +kernel
def extra198 (r : Fin 16) : Fin 128 := (#[82,83,86,87,90,91,94,95,114,115,118,119,122,123,126,127] : Array (Fin 128))[r.val]?.getD 0

theorem small198 : NoAtMost i4 (PetersenPackedPin.project extra198 tgt) 2 := by
  have h : PetersenPackedPin.project extra198 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot198 : forcedConst extra198 tgt = false := by decide +kernel
def extra199 (r : Fin 16) : Fin 128 := (#[0,1,16,17,8,9,24,25,4,5,20,21,12,13,28,29] : Array (Fin 128))[r.val]?.getD 0

theorem small199 : NoAtMost i4 (PetersenPackedPin.project extra199 tgt) 3 := by
  have h : PetersenPackedPin.project extra199 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot199 : forcedConst extra199 tgt = false := by decide +kernel
def extra200 (r : Fin 16) : Fin 128 := (#[64,65,80,81,72,73,88,89,68,69,84,85,76,77,92,93] : Array (Fin 128))[r.val]?.getD 0

theorem small200 : NoAtMost i4 (PetersenPackedPin.project extra200 tgt) 2 := by
  have h : PetersenPackedPin.project extra200 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot200 : forcedConst extra200 tgt = false := by decide +kernel
def extra201 (r : Fin 16) : Fin 128 := (#[32,36,40,44,48,52,56,60,33,37,41,45,49,53,57,61] : Array (Fin 128))[r.val]?.getD 0

theorem small201 : NoAtMost i4 (PetersenPackedPin.project extra201 tgt) 2 := by
  have h : PetersenPackedPin.project extra201 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot201 : forcedConst extra201 tgt = false := by decide +kernel
def extra202 (r : Fin 16) : Fin 128 := (#[66,74,82,90,67,75,83,91,70,78,86,94,71,79,87,95] : Array (Fin 128))[r.val]?.getD 0

theorem small202 : NoAtMost i4 (PetersenPackedPin.project extra202 tgt) 2 := by
  have h : PetersenPackedPin.project extra202 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot202 : forcedConst extra202 tgt = false := by decide +kernel
def extra203 (r : Fin 16) : Fin 128 := (#[34,42,50,58,35,43,51,59,38,46,54,62,39,47,55,63] : Array (Fin 128))[r.val]?.getD 0

theorem small203 : NoAtMost i4 (PetersenPackedPin.project extra203 tgt) 2 := by
  have h : PetersenPackedPin.project extra203 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot203 : forcedConst extra203 tgt = false := by decide +kernel
def extra204 (r : Fin 8) : Fin 128 := (#[16,48,80,112,17,49,81,113] : Array (Fin 128))[r.val]?.getD 0

theorem small204 : NoAtMost i3 (PetersenPackedPin.project extra204 tgt) 1 := by
  have h : PetersenPackedPin.project extra204 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot204 : forcedConst extra204 tgt = false := by decide +kernel
def extra205 (r : Fin 16) : Fin 128 := (#[8,10,9,11,40,42,41,43,72,74,73,75,104,106,105,107] : Array (Fin 128))[r.val]?.getD 0

theorem small205 : NoAtMost i4 (PetersenPackedPin.project extra205 tgt) 3 := by
  have h : PetersenPackedPin.project extra205 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot205 : forcedConst extra205 tgt = false := by decide +kernel
def extra206 (r : Fin 16) : Fin 128 := (#[4,5,36,37,6,7,38,39,68,69,100,101,70,71,102,103] : Array (Fin 128))[r.val]?.getD 0

theorem small206 : NoAtMost i4 (PetersenPackedPin.project extra206 tgt) 2 := by
  have h : PetersenPackedPin.project extra206 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot206 : forcedConst extra206 tgt = false := by decide +kernel
def extra207 (r : Fin 8) : Fin 128 := (#[20,21,22,23,84,85,86,87] : Array (Fin 128))[r.val]?.getD 0

theorem small207 : NoAtMost i3 (PetersenPackedPin.project extra207 tgt) 1 := by
  have h : PetersenPackedPin.project extra207 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot207 : forcedConst extra207 tgt = false := by decide +kernel
def extra208 (r : Fin 8) : Fin 128 := (#[0,2,1,3,16,18,17,19] : Array (Fin 128))[r.val]?.getD 0

theorem small208 : NoAtMost i3 (PetersenPackedPin.project extra208 tgt) 1 := by
  have h : PetersenPackedPin.project extra208 tgt = (0xc8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b7_0
theorem hot208 : forcedConst extra208 tgt = false := by decide +kernel
def extra209 (r : Fin 8) : Fin 128 := (#[8,9,10,11,24,25,26,27] : Array (Fin 128))[r.val]?.getD 0

theorem small209 : NoAtMost i3 (PetersenPackedPin.project extra209 tgt) 1 := by
  have h : PetersenPackedPin.project extra209 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot209 : forcedConst extra209 tgt = false := by decide +kernel
def extra210 (r : Fin 8) : Fin 128 := (#[40,41,56,57,104,105,120,121] : Array (Fin 128))[r.val]?.getD 0

theorem small210 : NoAtMost i3 (PetersenPackedPin.project extra210 tgt) 1 := by
  have h : PetersenPackedPin.project extra210 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot210 : forcedConst extra210 tgt = false := by decide +kernel
def extra211 (r : Fin 16) : Fin 128 := (#[4,5,20,21,6,7,22,23,68,69,84,85,70,71,86,87] : Array (Fin 128))[r.val]?.getD 0

theorem small211 : NoAtMost i4 (PetersenPackedPin.project extra211 tgt) 2 := by
  have h : PetersenPackedPin.project extra211 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot211 : forcedConst extra211 tgt = false := by decide +kernel
def extra212 (r : Fin 8) : Fin 128 := (#[36,37,38,39,100,101,102,103] : Array (Fin 128))[r.val]?.getD 0

theorem small212 : NoAtMost i3 (PetersenPackedPin.project extra212 tgt) 1 := by
  have h : PetersenPackedPin.project extra212 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot212 : forcedConst extra212 tgt = false := by decide +kernel
def extra213 (r : Fin 16) : Fin 128 := (#[0,1,2,3,16,17,18,19,32,33,34,35,48,49,50,51] : Array (Fin 128))[r.val]?.getD 0

theorem small213 : NoAtMost i4 (PetersenPackedPin.project extra213 tgt) 2 := by
  have h : PetersenPackedPin.project extra213 tgt = (0xaaa8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b51_0
theorem hot213 : forcedConst extra213 tgt = false := by decide +kernel
def extra214 (r : Fin 16) : Fin 128 := (#[64,66,65,67,80,82,81,83,96,98,97,99,112,114,113,115] : Array (Fin 128))[r.val]?.getD 0

theorem small214 : NoAtMost i4 (PetersenPackedPin.project extra214 tgt) 2 := by
  have h : PetersenPackedPin.project extra214 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot214 : forcedConst extra214 tgt = false := by decide +kernel
def extra215 (r : Fin 16) : Fin 128 := (#[8,10,9,11,40,42,41,43,24,26,25,27,56,58,57,59] : Array (Fin 128))[r.val]?.getD 0

theorem small215 : NoAtMost i4 (PetersenPackedPin.project extra215 tgt) 2 := by
  have h : PetersenPackedPin.project extra215 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot215 : forcedConst extra215 tgt = false := by decide +kernel
def extra216 (r : Fin 16) : Fin 128 := (#[72,73,74,75,88,89,90,91,104,105,106,107,120,121,122,123] : Array (Fin 128))[r.val]?.getD 0

theorem small216 : NoAtMost i4 (PetersenPackedPin.project extra216 tgt) 2 := by
  have h : PetersenPackedPin.project extra216 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot216 : forcedConst extra216 tgt = false := by decide +kernel
def extra217 (r : Fin 16) : Fin 128 := (#[4,20,5,21,36,52,37,53,6,22,7,23,38,54,39,55] : Array (Fin 128))[r.val]?.getD 0

theorem small217 : NoAtMost i4 (PetersenPackedPin.project extra217 tgt) 2 := by
  have h : PetersenPackedPin.project extra217 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot217 : forcedConst extra217 tgt = false := by decide +kernel
def extra218 (r : Fin 4) : Fin 128 := (#[0,1,2,3] : Array (Fin 128))[r.val]?.getD 0

theorem small218 : NoAtMost i2 (PetersenPackedPin.project extra218 tgt) 0 := by
  have h : PetersenPackedPin.project extra218 tgt = (0x8 : BitVec 4) := by decide +kernel
  rw [h]; exact Extra191.b3_0
theorem hot218 : forcedConst extra218 tgt = false := by decide +kernel
def extra219 (r : Fin 16) : Fin 128 := (#[52,53,54,55,60,61,62,63,116,117,118,119,124,125,126,127] : Array (Fin 128))[r.val]?.getD 0

theorem small219 : NoAtMost i4 (PetersenPackedPin.project extra219 tgt) 2 := by
  have h : PetersenPackedPin.project extra219 tgt = (0xfffe : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b0_4
theorem hot219 : forcedConst extra219 tgt = false := by decide +kernel
def extra220 (r : Fin 8) : Fin 128 := (#[0,2,1,3,32,34,33,35] : Array (Fin 128))[r.val]?.getD 0

theorem small220 : NoAtMost i3 (PetersenPackedPin.project extra220 tgt) 1 := by
  have h : PetersenPackedPin.project extra220 tgt = (0xc8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b7_0
theorem hot220 : forcedConst extra220 tgt = false := by decide +kernel
def extra221 (r : Fin 8) : Fin 128 := (#[64,65,66,67,96,97,98,99] : Array (Fin 128))[r.val]?.getD 0

theorem small221 : NoAtMost i3 (PetersenPackedPin.project extra221 tgt) 1 := by
  have h : PetersenPackedPin.project extra221 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot221 : forcedConst extra221 tgt = false := by decide +kernel
def extra222 (r : Fin 8) : Fin 128 := (#[80,81,88,89,112,113,120,121] : Array (Fin 128))[r.val]?.getD 0

theorem small222 : NoAtMost i3 (PetersenPackedPin.project extra222 tgt) 1 := by
  have h : PetersenPackedPin.project extra222 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot222 : forcedConst extra222 tgt = false := by decide +kernel
def extra223 (r : Fin 16) : Fin 128 := (#[4,5,36,37,6,7,38,39,12,13,44,45,14,15,46,47] : Array (Fin 128))[r.val]?.getD 0

theorem small223 : NoAtMost i4 (PetersenPackedPin.project extra223 tgt) 2 := by
  have h : PetersenPackedPin.project extra223 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot223 : forcedConst extra223 tgt = false := by decide +kernel
def extra224 (r : Fin 8) : Fin 128 := (#[20,21,22,23,28,29,30,31] : Array (Fin 128))[r.val]?.getD 0

theorem small224 : NoAtMost i3 (PetersenPackedPin.project extra224 tgt) 1 := by
  have h : PetersenPackedPin.project extra224 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot224 : forcedConst extra224 tgt = false := by decide +kernel
def extra225 (r : Fin 16) : Fin 128 := (#[64,66,65,67,80,82,81,83,72,74,73,75,88,90,89,91] : Array (Fin 128))[r.val]?.getD 0

theorem small225 : NoAtMost i4 (PetersenPackedPin.project extra225 tgt) 3 := by
  have h : PetersenPackedPin.project extra225 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot225 : forcedConst extra225 tgt = false := by decide +kernel
def extra226 (r : Fin 8) : Fin 128 := (#[32,40,48,56,33,41,49,57] : Array (Fin 128))[r.val]?.getD 0

theorem small226 : NoAtMost i3 (PetersenPackedPin.project extra226 tgt) 1 := by
  have h : PetersenPackedPin.project extra226 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot226 : forcedConst extra226 tgt = false := by decide +kernel
def extra227 (r : Fin 16) : Fin 128 := (#[4,5,20,21,6,7,22,23,12,13,28,29,14,15,30,31] : Array (Fin 128))[r.val]?.getD 0

theorem small227 : NoAtMost i4 (PetersenPackedPin.project extra227 tgt) 2 := by
  have h : PetersenPackedPin.project extra227 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot227 : forcedConst extra227 tgt = false := by decide +kernel
def extra228 (r : Fin 8) : Fin 128 := (#[36,37,38,39,44,45,46,47] : Array (Fin 128))[r.val]?.getD 0

theorem small228 : NoAtMost i3 (PetersenPackedPin.project extra228 tgt) 1 := by
  have h : PetersenPackedPin.project extra228 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot228 : forcedConst extra228 tgt = false := by decide +kernel
def extra229 (r : Fin 16) : Fin 128 := (#[0,1,2,3,4,5,6,7,64,65,66,67,68,69,70,71] : Array (Fin 128))[r.val]?.getD 0

theorem small229 : NoAtMost i4 (PetersenPackedPin.project extra229 tgt) 3 := by
  have h : PetersenPackedPin.project extra229 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot229 : forcedConst extra229 tgt = false := by decide +kernel
def extra230 (r : Fin 16) : Fin 128 := (#[16,18,20,22,80,82,84,86,17,19,21,23,81,83,85,87] : Array (Fin 128))[r.val]?.getD 0

theorem small230 : NoAtMost i4 (PetersenPackedPin.project extra230 tgt) 2 := by
  have h : PetersenPackedPin.project extra230 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot230 : forcedConst extra230 tgt = false := by decide +kernel
def extra231 (r : Fin 16) : Fin 128 := (#[48,50,52,54,49,51,53,55,112,114,116,118,113,115,117,119] : Array (Fin 128))[r.val]?.getD 0

theorem small231 : NoAtMost i4 (PetersenPackedPin.project extra231 tgt) 2 := by
  have h : PetersenPackedPin.project extra231 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot231 : forcedConst extra231 tgt = false := by decide +kernel
def extra232 (r : Fin 8) : Fin 128 := (#[8,9,10,11,12,13,14,15] : Array (Fin 128))[r.val]?.getD 0

theorem small232 : NoAtMost i3 (PetersenPackedPin.project extra232 tgt) 1 := by
  have h : PetersenPackedPin.project extra232 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot232 : forcedConst extra232 tgt = false := by decide +kernel
def extra233 (r : Fin 8) : Fin 128 := (#[40,41,44,45,104,105,108,109] : Array (Fin 128))[r.val]?.getD 0

theorem small233 : NoAtMost i3 (PetersenPackedPin.project extra233 tgt) 1 := by
  have h : PetersenPackedPin.project extra233 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot233 : forcedConst extra233 tgt = false := by decide +kernel
def extra234 (r : Fin 16) : Fin 128 := (#[0,4,2,6,1,5,3,7,32,36,34,38,33,37,35,39] : Array (Fin 128))[r.val]?.getD 0

theorem small234 : NoAtMost i4 (PetersenPackedPin.project extra234 tgt) 3 := by
  have h : PetersenPackedPin.project extra234 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot234 : forcedConst extra234 tgt = false := by decide +kernel
def extra235 (r : Fin 8) : Fin 128 := (#[16,18,20,22,17,19,21,23] : Array (Fin 128))[r.val]?.getD 0

theorem small235 : NoAtMost i3 (PetersenPackedPin.project extra235 tgt) 1 := by
  have h : PetersenPackedPin.project extra235 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot235 : forcedConst extra235 tgt = false := by decide +kernel
def extra236 (r : Fin 8) : Fin 128 := (#[80,81,84,85,112,113,116,117] : Array (Fin 128))[r.val]?.getD 0

theorem small236 : NoAtMost i3 (PetersenPackedPin.project extra236 tgt) 1 := by
  have h : PetersenPackedPin.project extra236 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot236 : forcedConst extra236 tgt = false := by decide +kernel
def extra237 (r : Fin 16) : Fin 128 := (#[8,10,9,11,40,42,41,43,12,14,13,15,44,46,45,47] : Array (Fin 128))[r.val]?.getD 0

theorem small237 : NoAtMost i4 (PetersenPackedPin.project extra237 tgt) 2 := by
  have h : PetersenPackedPin.project extra237 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot237 : forcedConst extra237 tgt = false := by decide +kernel
def extra238 (r : Fin 16) : Fin 128 := (#[72,73,74,75,76,77,78,79,104,105,106,107,108,109,110,111] : Array (Fin 128))[r.val]?.getD 0

theorem small238 : NoAtMost i4 (PetersenPackedPin.project extra238 tgt) 2 := by
  have h : PetersenPackedPin.project extra238 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot238 : forcedConst extra238 tgt = false := by decide +kernel
def extra239 (r : Fin 16) : Fin 128 := (#[0,4,2,6,1,5,3,7,16,20,18,22,17,21,19,23] : Array (Fin 128))[r.val]?.getD 0

theorem small239 : NoAtMost i4 (PetersenPackedPin.project extra239 tgt) 3 := by
  have h : PetersenPackedPin.project extra239 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot239 : forcedConst extra239 tgt = false := by decide +kernel
def extra240 (r : Fin 16) : Fin 128 := (#[64,66,65,67,80,82,81,83,68,70,69,71,84,86,85,87] : Array (Fin 128))[r.val]?.getD 0

theorem small240 : NoAtMost i4 (PetersenPackedPin.project extra240 tgt) 2 := by
  have h : PetersenPackedPin.project extra240 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot240 : forcedConst extra240 tgt = false := by decide +kernel
def extra241 (r : Fin 8) : Fin 128 := (#[32,34,36,38,33,35,37,39] : Array (Fin 128))[r.val]?.getD 0

theorem small241 : NoAtMost i3 (PetersenPackedPin.project extra241 tgt) 1 := by
  have h : PetersenPackedPin.project extra241 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot241 : forcedConst extra241 tgt = false := by decide +kernel
def extra242 (r : Fin 16) : Fin 128 := (#[72,73,74,75,76,77,78,79,88,89,90,91,92,93,94,95] : Array (Fin 128))[r.val]?.getD 0

theorem small242 : NoAtMost i4 (PetersenPackedPin.project extra242 tgt) 2 := by
  have h : PetersenPackedPin.project extra242 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot242 : forcedConst extra242 tgt = false := by decide +kernel
def extra243 (r : Fin 8) : Fin 128 := (#[40,41,44,45,56,57,60,61] : Array (Fin 128))[r.val]?.getD 0

theorem small243 : NoAtMost i3 (PetersenPackedPin.project extra243 tgt) 1 := by
  have h : PetersenPackedPin.project extra243 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot243 : forcedConst extra243 tgt = false := by decide +kernel
def extra244 (r : Fin 16) : Fin 128 := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 128))[r.val]?.getD 0

theorem small244 : NoAtMost i4 (PetersenPackedPin.project extra244 tgt) 3 := by
  have h : PetersenPackedPin.project extra244 tgt = (0xf8c8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b15_0
theorem hot244 : forcedConst extra244 tgt = false := by decide +kernel
def extra245 (r : Fin 8) : Fin 128 := (#[64,65,66,67,68,69,70,71] : Array (Fin 128))[r.val]?.getD 0

theorem small245 : NoAtMost i3 (PetersenPackedPin.project extra245 tgt) 1 := by
  have h : PetersenPackedPin.project extra245 tgt = (0xf8 : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b3_1
theorem hot245 : forcedConst extra245 tgt = false := by decide +kernel
def extra246 (r : Fin 16) : Fin 128 := (#[32,34,36,38,40,42,44,46,33,35,37,39,41,43,45,47] : Array (Fin 128))[r.val]?.getD 0

theorem small246 : NoAtMost i4 (PetersenPackedPin.project extra246 tgt) 2 := by
  have h : PetersenPackedPin.project extra246 tgt = (0xffc8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b7_1
theorem hot246 : forcedConst extra246 tgt = false := by decide +kernel
def extra247 (r : Fin 8) : Fin 128 := (#[80,81,84,85,88,89,92,93] : Array (Fin 128))[r.val]?.getD 0

theorem small247 : NoAtMost i3 (PetersenPackedPin.project extra247 tgt) 1 := by
  have h : PetersenPackedPin.project extra247 tgt = (0xfe : BitVec 8) := by decide +kernel
  rw [h]; exact Extra191.b0_3
theorem hot247 : forcedConst extra247 tgt = false := by decide +kernel
def extra248 (r : Fin 16) : Fin 128 := (#[48,50,52,54,49,51,53,55,56,58,60,62,57,59,61,63] : Array (Fin 128))[r.val]?.getD 0

theorem small248 : NoAtMost i4 (PetersenPackedPin.project extra248 tgt) 2 := by
  have h : PetersenPackedPin.project extra248 tgt = (0xfff8 : BitVec 16) := by decide +kernel
  rw [h]; exact Extra191.b3_2
theorem hot248 : forcedConst extra248 tgt = false := by decide +kernel
end Deleted191Cost10
