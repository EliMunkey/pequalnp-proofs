import PetersenComponentLifts
import PetersenBareBases
import Cost3
import Cost7
import M189Closing
open PetersenWordCost
namespace Extra191
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b0_2 : NoAtMost ([0xa,0xc] : List (BitVec 4)) 0xe 0 := by
  apply lower_of_reject
  apply rejectBool_sound
  decide
theorem b0_3 : NoAtMost ([0xaa,0xcc,0xf0] : List (BitVec 8)) 0xfe 1 := by
  apply lift_pin (insertRow 2 2 false) (insertRow 2 2 true) b0_2 <;> decide +kernel
theorem b0_4 : NoAtMost ([0xaaaa,0xcccc,0xf0f0,0xff00] : List (BitVec 16)) 0xfffe 2 := by
  apply lift_pin (insertRow 3 3 false) (insertRow 3 3 true) b0_3 <;> decide +kernel
theorem b0_5 : NoAtMost ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] : List (BitVec 32)) 0xfffffffe 3 := by
  apply lift_pin (insertRow 4 4 false) (insertRow 4 4 true) b0_4 <;> decide +kernel
theorem b3_0 : NoAtMost ([0xa,0xc] : List (BitVec 4)) 0x8 0 := by
  exact PetersenGraphCosts.mask3_lower
theorem b3_1 : NoAtMost ([0xaa,0xcc,0xf0] : List (BitVec 8)) 0xf8 1 := by
  apply lift_pin (insertRow 2 2 false) (insertRow 2 2 true) b3_0 <;> decide +kernel
theorem b3_2 : NoAtMost ([0xaaaa,0xcccc,0xf0f0,0xff00] : List (BitVec 16)) 0xfff8 2 := by
  apply lift_pin (insertRow 3 3 false) (insertRow 3 3 true) b3_1 <;> decide +kernel
theorem b3_3 : NoAtMost ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] : List (BitVec 32)) 0xfffffff8 3 := by
  apply lift_pin (insertRow 4 4 false) (insertRow 4 4 true) b3_2 <;> decide +kernel
theorem b7_0 : NoAtMost ([0xaa,0xcc,0xf0] : List (BitVec 8)) 0xc8 1 := by
  exact PetersenGraphCosts.mask7_lower
theorem b7_1 : NoAtMost ([0xaaaa,0xcccc,0xf0f0,0xff00] : List (BitVec 16)) 0xffc8 2 := by
  apply lift_pin (insertRow 3 3 false) (insertRow 3 3 true) b7_0 <;> decide +kernel
theorem b7_2 : NoAtMost ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] : List (BitVec 32)) 0xffffffc8 3 := by
  apply lift_pin (insertRow 4 4 false) (insertRow 4 4 true) b7_1 <;> decide +kernel
theorem b7_3 : NoAtMost ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] : List (BitVec 64)) 0xffffffffffffffc8 4 := by
  apply lift_pin (insertRow 5 5 false) (insertRow 5 5 true) b7_2 <;> decide +kernel
theorem b15_0 : NoAtMost ([0xaaaa,0xcccc,0xf0f0,0xff00] : List (BitVec 16)) 0xf8c8 3 := by
  exact PetersenGraphCosts.mask15_lower
theorem b15_1 : NoAtMost ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] : List (BitVec 32)) 0xfffff8c8 4 := by
  apply lift_pin (insertRow 4 4 false) (insertRow 4 4 true) b15_0 <;> decide +kernel
theorem b15_2 : NoAtMost ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] : List (BitVec 64)) 0xfffffffffffff8c8 5 := by
  apply lift_pin (insertRow 5 5 false) (insertRow 5 5 true) b15_1 <;> decide +kernel
theorem b45_0 : NoAtMost ([0xaaaa,0xcccc,0xf0f0,0xff00] : List (BitVec 16)) 0xeac0 2 := by
  exact PetersenGraphCosts.mask45_lower
theorem b45_1 : NoAtMost ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] : List (BitVec 32)) 0xffffeac0 3 := by
  apply lift_pin (insertRow 4 4 false) (insertRow 4 4 true) b45_0 <;> decide +kernel
theorem b45_2 : NoAtMost ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] : List (BitVec 64)) 0xffffffffffffeac0 4 := by
  apply lift_pin (insertRow 5 5 false) (insertRow 5 5 true) b45_1 <;> decide +kernel
theorem b47_0 : NoAtMost ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] : List (BitVec 32)) 0xfaeaf8c8 4 := by
  exact PetersenGraphCosts.mask47_lower
theorem b51_0 : NoAtMost ([0xaaaa,0xcccc,0xf0f0,0xff00] : List (BitVec 16)) 0xaaa8 2 := by
  exact PetersenGraphCosts.mask51_lower
theorem b55_0 : NoAtMost ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] : List (BitVec 32)) 0xeaeaeac8 4 := by
  exact PetersenGraphCosts.mask55_lower
end Extra191
