import Extra1020K12
import PetersenPackedPin
import PetersenLayerCheck
import Q1020Symmetry
open PetersenWordCost PetersenPackedPin
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0
abbrev tgt := Q1020Symmetry.target
def i5 : List (BitVec 32) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def i6 : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def i7 : List (BitVec 128) := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
def cycle0 (r : Fin 32) : Fin 256 := (#[0,1,2,3,4,5,6,7,128,129,130,131,132,133,134,135,32,33,34,35,36,37,38,39,160,161,162,163,164,165,166,167] : Array (Fin 256))[r.val]?.getD 0
theorem small0 : NoAtMost i5 (PetersenPackedPin.project cycle0 tgt) 6 := by
  have h : PetersenPackedPin.project cycle0 tgt = (0xffeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact PetersenCycleFive.no_six_gates
theorem hot0 : forcedConst cycle0 tgt = false := by decide +kernel
def cycle1 (r : Fin 32) : Fin 256 := (#[0,1,2,3,64,65,66,67,8,9,10,11,72,73,74,75,32,33,34,35,96,97,98,99,40,41,42,43,104,105,106,107] : Array (Fin 256))[r.val]?.getD 0
theorem small1 : NoAtMost i5 (PetersenPackedPin.project cycle1 tgt) 6 := by
  have h : PetersenPackedPin.project cycle1 tgt = (0xffeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact PetersenCycleFive.no_six_gates
theorem hot1 : forcedConst cycle1 tgt = false := by decide +kernel
def cycle2 (r : Fin 32) : Fin 256 := (#[0,2,4,6,128,130,132,134,16,18,20,22,144,146,148,150,64,66,68,70,192,194,196,198,80,82,84,86,208,210,212,214] : Array (Fin 256))[r.val]?.getD 0
theorem small2 : NoAtMost i5 (PetersenPackedPin.project cycle2 tgt) 6 := by
  have h : PetersenPackedPin.project cycle2 tgt = (0xffeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact PetersenCycleFive.no_six_gates
theorem hot2 : forcedConst cycle2 tgt = false := by decide +kernel
def cycle3 (r : Fin 32) : Fin 256 := (#[0,8,32,40,128,136,160,168,16,24,48,56,144,152,176,184,64,72,96,104,192,200,224,232,80,88,112,120,208,216,240,248] : Array (Fin 256))[r.val]?.getD 0
theorem small3 : NoAtMost i5 (PetersenPackedPin.project cycle3 tgt) 6 := by
  have h : PetersenPackedPin.project cycle3 tgt = (0xffeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact PetersenCycleFive.no_six_gates
theorem hot3 : forcedConst cycle3 tgt = false := by decide +kernel
def tree16 (r : Fin 64) : Fin 256 := (#[0,4,2,6,64,68,66,70,8,12,10,14,72,76,74,78,128,132,130,134,192,196,194,198,136,140,138,142,200,204,202,206,1,5,3,7,65,69,67,71,9,13,11,15,73,77,75,79,129,133,131,135,193,197,195,199,137,141,139,143,201,205,203,207] : Array (Fin 256))[r.val]?.getD 0
theorem small16 : NoAtMost i6 (PetersenPackedPin.project tree16 tgt) 6 := by
  have h : PetersenPackedPin.project tree16 tgt = (0xfeeefcccfaeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact PetersenGraphCosts.M111.bound
theorem hot16 : forcedConst tree16 tgt = false := by decide +kernel
def tree17 (r : Fin 64) : Fin 256 := (#[0,1,2,3,64,65,66,67,16,17,18,19,80,81,82,83,32,33,34,35,96,97,98,99,48,49,50,51,112,113,114,115,4,5,6,7,68,69,70,71,20,21,22,23,84,85,86,87,36,37,38,39,100,101,102,103,52,53,54,55,116,117,118,119] : Array (Fin 256))[r.val]?.getD 0
theorem small17 : NoAtMost i6 (PetersenPackedPin.project tree17 tgt) 6 := by
  have h : PetersenPackedPin.project tree17 tgt = (0xfeeefcccfaeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact PetersenGraphCosts.M111.bound
theorem hot17 : forcedConst tree17 tgt = false := by decide +kernel
def tree18 (r : Fin 64) : Fin 256 := (#[0,1,32,33,128,129,160,161,16,17,48,49,144,145,176,177,2,3,34,35,130,131,162,163,18,19,50,51,146,147,178,179,8,9,40,41,136,137,168,169,24,25,56,57,152,153,184,185,10,11,42,43,138,139,170,171,26,27,58,59,154,155,186,187] : Array (Fin 256))[r.val]?.getD 0
theorem small18 : NoAtMost i6 (PetersenPackedPin.project tree18 tgt) 6 := by
  have h : PetersenPackedPin.project tree18 tgt = (0xfeeefcccfaeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact PetersenGraphCosts.M111.bound
theorem hot18 : forcedConst tree18 tgt = false := by decide +kernel
def tree19 (r : Fin 64) : Fin 256 := (#[0,2,64,66,16,18,80,82,128,130,192,194,144,146,208,210,1,3,65,67,17,19,81,83,129,131,193,195,145,147,209,211,8,10,72,74,24,26,88,90,136,138,200,202,152,154,216,218,9,11,73,75,25,27,89,91,137,139,201,203,153,155,217,219] : Array (Fin 256))[r.val]?.getD 0
theorem small19 : NoAtMost i6 (PetersenPackedPin.project tree19 tgt) 6 := by
  have h : PetersenPackedPin.project tree19 tgt = (0xfeeefcccfaeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact PetersenGraphCosts.M111.bound
theorem hot19 : forcedConst tree19 tgt = false := by decide +kernel
def tree20 (r : Fin 64) : Fin 256 := (#[0,8,32,40,128,136,160,168,4,12,36,44,132,140,164,172,64,72,96,104,192,200,224,232,68,76,100,108,196,204,228,236,1,9,33,41,129,137,161,169,5,13,37,45,133,141,165,173,65,73,97,105,193,201,225,233,69,77,101,109,197,205,229,237] : Array (Fin 256))[r.val]?.getD 0
theorem small20 : NoAtMost i6 (PetersenPackedPin.project tree20 tgt) 6 := by
  have h : PetersenPackedPin.project tree20 tgt = (0xfeeefcccfaeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact PetersenGraphCosts.M111.bound
theorem hot20 : forcedConst tree20 tgt = false := by decide +kernel
def tree21 (r : Fin 64) : Fin 256 := (#[0,16,128,144,32,48,160,176,1,17,129,145,33,49,161,177,64,80,192,208,96,112,224,240,65,81,193,209,97,113,225,241,4,20,132,148,36,52,164,180,5,21,133,149,37,53,165,181,68,84,196,212,100,116,228,244,69,85,197,213,101,117,229,245] : Array (Fin 256))[r.val]?.getD 0
theorem small21 : NoAtMost i6 (PetersenPackedPin.project tree21 tgt) 6 := by
  have h : PetersenPackedPin.project tree21 tgt = (0xfeeefcccfaeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact PetersenGraphCosts.M111.bound
theorem hot21 : forcedConst tree21 tgt = false := by decide +kernel
def tree22 (r : Fin 64) : Fin 256 := (#[0,2,64,66,8,10,72,74,32,34,96,98,40,42,104,106,4,6,68,70,12,14,76,78,36,38,100,102,44,46,108,110,16,18,80,82,24,26,88,90,48,50,112,114,56,58,120,122,20,22,84,86,28,30,92,94,52,54,116,118,60,62,124,126] : Array (Fin 256))[r.val]?.getD 0
theorem small22 : NoAtMost i6 (PetersenPackedPin.project tree22 tgt) 6 := by
  have h : PetersenPackedPin.project tree22 tgt = (0xfeeefcccfaeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact PetersenGraphCosts.M111.bound
theorem hot22 : forcedConst tree22 tgt = false := by decide +kernel
def tree23 (r : Fin 64) : Fin 256 := (#[0,4,128,132,32,36,160,164,8,12,136,140,40,44,168,172,2,6,130,134,34,38,162,166,10,14,138,142,42,46,170,174,16,20,144,148,48,52,176,180,24,28,152,156,56,60,184,188,18,22,146,150,50,54,178,182,26,30,154,158,58,62,186,190] : Array (Fin 256))[r.val]?.getD 0
theorem small23 : NoAtMost i6 (PetersenPackedPin.project tree23 tgt) 6 := by
  have h : PetersenPackedPin.project tree23 tgt = (0xfeeefcccfaeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact PetersenGraphCosts.M111.bound
theorem hot23 : forcedConst tree23 tgt = false := by decide +kernel
def extra26 (r : Fin 128) : Fin 256 := (#[0,64,16,80,128,192,144,208,4,68,20,84,132,196,148,212,2,66,18,82,130,194,146,210,6,70,22,86,134,198,150,214,8,72,24,88,136,200,152,216,12,76,28,92,140,204,156,220,10,74,26,90,138,202,154,218,14,78,30,94,142,206,158,222,32,96,48,112,160,224,176,240,36,100,52,116,164,228,180,244,34,98,50,114,162,226,178,242,38,102,54,118,166,230,182,246,40,104,56,120,168,232,184,248,44,108,60,124,172,236,188,252,42,106,58,122,170,234,186,250,46,110,62,126,174,238,190,254] : Array (Fin 256))[r.val]?.getD 0
theorem small26 (theta : Extra1020K12.Theta) : NoAtMost i7 (PetersenPackedPin.project extra26 tgt) 10 := by
  have h : PetersenPackedPin.project extra26 tgt = (0xfffffffffffaf8f8ffeafaeaffeaf8c8 : BitVec 128) := by decide +kernel
  rw [h]; exact Extra1020K12.b191_0 theta
theorem hot26 : forcedConst extra26 tgt = false := by decide +kernel
def extra27 (r : Fin 128) : Fin 256 := (#[1,65,17,81,129,193,145,209,5,69,21,85,133,197,149,213,9,73,25,89,137,201,153,217,13,77,29,93,141,205,157,221,3,67,19,83,131,195,147,211,7,71,23,87,135,199,151,215,11,75,27,91,139,203,155,219,15,79,31,95,143,207,159,223,33,97,49,113,161,225,177,241,37,101,53,117,165,229,181,245,41,105,57,121,169,233,185,249,45,109,61,125,173,237,189,253,35,99,51,115,163,227,179,243,39,103,55,119,167,231,183,247,43,107,59,123,171,235,187,251,47,111,63,127,175,239,191,255] : Array (Fin 256))[r.val]?.getD 0
theorem small27 : NoAtMost i7 (PetersenPackedPin.project extra27 tgt) 6 := by
  have h : PetersenPackedPin.project extra27 tgt = (0xfffffffffffffffffffffffffaeaf8c8 : BitVec 128) := by decide +kernel
  rw [h]; exact Extra1020K12.b47_2
theorem hot27 : forcedConst extra27 tgt = false := by decide +kernel
def extra29 (r : Fin 128) : Fin 256 := (#[2,10,34,42,130,138,162,170,18,26,50,58,146,154,178,186,3,11,35,43,131,139,163,171,19,27,51,59,147,155,179,187,6,14,38,46,134,142,166,174,22,30,54,62,150,158,182,190,7,15,39,47,135,143,167,175,23,31,55,63,151,159,183,191,66,74,98,106,194,202,226,234,82,90,114,122,210,218,242,250,67,75,99,107,195,203,227,235,83,91,115,123,211,219,243,251,70,78,102,110,198,206,230,238,86,94,118,126,214,222,246,254,71,79,103,111,199,207,231,239,87,95,119,127,215,223,247,255] : Array (Fin 256))[r.val]?.getD 0
theorem small29 : NoAtMost i7 (PetersenPackedPin.project extra29 tgt) 6 := by
  have h : PetersenPackedPin.project extra29 tgt = (0xfffffffffffffffffffffffffffff8c8 : BitVec 128) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_3
theorem hot29 : forcedConst extra29 tgt = false := by decide +kernel
def extra30 (r : Fin 128) : Fin 256 := (#[0,32,8,40,64,96,72,104,2,34,10,42,66,98,74,106,1,33,9,41,65,97,73,105,3,35,11,43,67,99,75,107,128,160,136,168,192,224,200,232,130,162,138,170,194,226,202,234,129,161,137,169,193,225,201,233,131,163,139,171,195,227,203,235,16,48,24,56,80,112,88,120,18,50,26,58,82,114,90,122,17,49,25,57,81,113,89,121,19,51,27,59,83,115,91,123,144,176,152,184,208,240,216,248,146,178,154,186,210,242,218,250,145,177,153,185,209,241,217,249,147,179,155,187,211,243,219,251] : Array (Fin 256))[r.val]?.getD 0
theorem small30 (theta : Extra1020K12.Theta) : NoAtMost i7 (PetersenPackedPin.project extra30 tgt) 10 := by
  have h : PetersenPackedPin.project extra30 tgt = (0xfffffffffffaf8f8ffeafaeaffeaf8c8 : BitVec 128) := by decide +kernel
  rw [h]; exact Extra1020K12.b191_0 theta
theorem hot30 : forcedConst extra30 tgt = false := by decide +kernel
def extra31 (r : Fin 128) : Fin 256 := (#[4,36,12,44,68,100,76,108,20,52,28,60,84,116,92,124,5,37,13,45,69,101,77,109,21,53,29,61,85,117,93,125,6,38,14,46,70,102,78,110,22,54,30,62,86,118,94,126,7,39,15,47,71,103,79,111,23,55,31,63,87,119,95,127,132,164,140,172,196,228,204,236,148,180,156,188,212,244,220,252,133,165,141,173,197,229,205,237,149,181,157,189,213,245,221,253,134,166,142,174,198,230,206,238,150,182,158,190,214,246,222,254,135,167,143,175,199,231,207,239,151,183,159,191,215,247,223,255] : Array (Fin 256))[r.val]?.getD 0
theorem small31 : NoAtMost i7 (PetersenPackedPin.project extra31 tgt) 6 := by
  have h : PetersenPackedPin.project extra31 tgt = (0xfffffffffffffffffffffffffaeaf8c8 : BitVec 128) := by decide +kernel
  rw [h]; exact Extra1020K12.b47_2
theorem hot31 : forcedConst extra31 tgt = false := by decide +kernel
def extra32 (r : Fin 128) : Fin 256 := (#[0,2,4,6,128,130,132,134,16,18,20,22,144,146,148,150,64,66,68,70,192,194,196,198,80,82,84,86,208,210,212,214,1,3,5,7,129,131,133,135,17,19,21,23,145,147,149,151,65,67,69,71,193,195,197,199,81,83,85,87,209,211,213,215,32,34,36,38,160,162,164,166,48,50,52,54,176,178,180,182,96,98,100,102,224,226,228,230,112,114,116,118,240,242,244,246,33,35,37,39,161,163,165,167,49,51,53,55,177,179,181,183,97,99,101,103,225,227,229,231,113,115,117,119,241,243,245,247] : Array (Fin 256))[r.val]?.getD 0
theorem small32 (theta : Extra1020K12.Theta) : NoAtMost i7 (PetersenPackedPin.project extra32 tgt) 10 := by
  have h : PetersenPackedPin.project extra32 tgt = (0xfffffffffffaf8f8ffeafaeaffeaf8c8 : BitVec 128) := by decide +kernel
  rw [h]; exact Extra1020K12.b191_0 theta
theorem hot32 : forcedConst extra32 tgt = false := by decide +kernel
def extra33 (r : Fin 128) : Fin 256 := (#[8,10,12,14,136,138,140,142,24,26,28,30,152,154,156,158,9,11,13,15,137,139,141,143,25,27,29,31,153,155,157,159,40,42,44,46,168,170,172,174,56,58,60,62,184,186,188,190,41,43,45,47,169,171,173,175,57,59,61,63,185,187,189,191,72,74,76,78,200,202,204,206,88,90,92,94,216,218,220,222,73,75,77,79,201,203,205,207,89,91,93,95,217,219,221,223,104,106,108,110,232,234,236,238,120,122,124,126,248,250,252,254,105,107,109,111,233,235,237,239,121,123,125,127,249,251,253,255] : Array (Fin 256))[r.val]?.getD 0
theorem small33 : NoAtMost i7 (PetersenPackedPin.project extra33 tgt) 6 := by
  have h : PetersenPackedPin.project extra33 tgt = (0xfffffffffffffffffffffffffaeaf8c8 : BitVec 128) := by decide +kernel
  rw [h]; exact Extra1020K12.b47_2
theorem hot33 : forcedConst extra33 tgt = false := by decide +kernel
def extra34 (r : Fin 128) : Fin 256 := (#[0,2,1,3,32,34,33,35,8,10,9,11,40,42,41,43,64,66,65,67,96,98,97,99,72,74,73,75,104,106,105,107,4,6,5,7,36,38,37,39,12,14,13,15,44,46,45,47,68,70,69,71,100,102,101,103,76,78,77,79,108,110,109,111,128,130,129,131,160,162,161,163,136,138,137,139,168,170,169,171,192,194,193,195,224,226,225,227,200,202,201,203,232,234,233,235,132,134,133,135,164,166,165,167,140,142,141,143,172,174,173,175,196,198,197,199,228,230,229,231,204,206,205,207,236,238,237,239] : Array (Fin 256))[r.val]?.getD 0
theorem small34 (theta : Extra1020K12.Theta) : NoAtMost i7 (PetersenPackedPin.project extra34 tgt) 10 := by
  have h : PetersenPackedPin.project extra34 tgt = (0xfffffffffffaf8f8ffeafaeaffeaf8c8 : BitVec 128) := by decide +kernel
  rw [h]; exact Extra1020K12.b191_0 theta
theorem hot34 : forcedConst extra34 tgt = false := by decide +kernel
def extra35 (r : Fin 128) : Fin 256 := (#[16,18,17,19,48,50,49,51,24,26,25,27,56,58,57,59,20,22,21,23,52,54,53,55,28,30,29,31,60,62,61,63,80,82,81,83,112,114,113,115,88,90,89,91,120,122,121,123,84,86,85,87,116,118,117,119,92,94,93,95,124,126,125,127,144,146,145,147,176,178,177,179,152,154,153,155,184,186,185,187,148,150,149,151,180,182,181,183,156,158,157,159,188,190,189,191,208,210,209,211,240,242,241,243,216,218,217,219,248,250,249,251,212,214,213,215,244,246,245,247,220,222,221,223,252,254,253,255] : Array (Fin 256))[r.val]?.getD 0
theorem small35 : NoAtMost i7 (PetersenPackedPin.project extra35 tgt) 6 := by
  have h : PetersenPackedPin.project extra35 tgt = (0xfffffffffffffffffffffffffaeaf8c8 : BitVec 128) := by decide +kernel
  rw [h]; exact Extra1020K12.b47_2
theorem hot35 : forcedConst extra35 tgt = false := by decide +kernel
def extra37 (r : Fin 128) : Fin 256 := (#[32,36,34,38,96,100,98,102,48,52,50,54,112,116,114,118,33,37,35,39,97,101,99,103,49,53,51,55,113,117,115,119,40,44,42,46,104,108,106,110,56,60,58,62,120,124,122,126,41,45,43,47,105,109,107,111,57,61,59,63,121,125,123,127,160,164,162,166,224,228,226,230,176,180,178,182,240,244,242,246,161,165,163,167,225,229,227,231,177,181,179,183,241,245,243,247,168,172,170,174,232,236,234,238,184,188,186,190,248,252,250,254,169,173,171,175,233,237,235,239,185,189,187,191,249,253,251,255] : Array (Fin 256))[r.val]?.getD 0
theorem small37 : NoAtMost i7 (PetersenPackedPin.project extra37 tgt) 6 := by
  have h : PetersenPackedPin.project extra37 tgt = (0xfffffffffffffffffffffffffffff8c8 : BitVec 128) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_3
theorem hot37 : forcedConst extra37 tgt = false := by decide +kernel
def extra39 (r : Fin 128) : Fin 256 := (#[64,65,96,97,192,193,224,225,68,69,100,101,196,197,228,229,66,67,98,99,194,195,226,227,70,71,102,103,198,199,230,231,72,73,104,105,200,201,232,233,76,77,108,109,204,205,236,237,74,75,106,107,202,203,234,235,78,79,110,111,206,207,238,239,80,81,112,113,208,209,240,241,84,85,116,117,212,213,244,245,82,83,114,115,210,211,242,243,86,87,118,119,214,215,246,247,88,89,120,121,216,217,248,249,92,93,124,125,220,221,252,253,90,91,122,123,218,219,250,251,94,95,126,127,222,223,254,255] : Array (Fin 256))[r.val]?.getD 0
theorem small39 : NoAtMost i7 (PetersenPackedPin.project extra39 tgt) 6 := by
  have h : PetersenPackedPin.project extra39 tgt = (0xfffffffffffffffffffffffffffff8c8 : BitVec 128) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_3
theorem hot39 : forcedConst extra39 tgt = false := by decide +kernel
def extra41 (r : Fin 128) : Fin 256 := (#[128,129,130,131,192,193,194,195,136,137,138,139,200,201,202,203,132,133,134,135,196,197,198,199,140,141,142,143,204,205,206,207,144,145,146,147,208,209,210,211,152,153,154,155,216,217,218,219,148,149,150,151,212,213,214,215,156,157,158,159,220,221,222,223,160,161,162,163,224,225,226,227,168,169,170,171,232,233,234,235,164,165,166,167,228,229,230,231,172,173,174,175,236,237,238,239,176,177,178,179,240,241,242,243,184,185,186,187,248,249,250,251,180,181,182,183,244,245,246,247,188,189,190,191,252,253,254,255] : Array (Fin 256))[r.val]?.getD 0
theorem small41 : NoAtMost i7 (PetersenPackedPin.project extra41 tgt) 6 := by
  have h : PetersenPackedPin.project extra41 tgt = (0xfffffffffffffffffffffffffffff8c8 : BitVec 128) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_3
theorem hot41 : forcedConst extra41 tgt = false := by decide +kernel
def extra42 (r : Fin 64) : Fin 256 := (#[2,10,34,42,130,138,162,170,18,26,50,58,146,154,178,186,6,14,38,46,134,142,166,174,22,30,54,62,150,158,182,190,66,74,98,106,194,202,226,234,82,90,114,122,210,218,242,250,70,78,102,110,198,206,230,238,86,94,118,126,214,222,246,254] : Array (Fin 256))[r.val]?.getD 0
theorem small42 : NoAtMost i6 (PetersenPackedPin.project extra42 tgt) 5 := by
  have h : PetersenPackedPin.project extra42 tgt = (0xfffffffffffff8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_2
theorem hot42 : forcedConst extra42 tgt = false := by decide +kernel
def extra54 (r : Fin 64) : Fin 256 := (#[1,65,17,81,129,193,145,209,5,69,21,85,133,197,149,213,9,73,25,89,137,201,153,217,13,77,29,93,141,205,157,221,3,67,19,83,131,195,147,211,7,71,23,87,135,199,151,215,11,75,27,91,139,203,155,219,15,79,31,95,143,207,159,223] : Array (Fin 256))[r.val]?.getD 0
theorem small54 : NoAtMost i6 (PetersenPackedPin.project extra54 tgt) 5 := by
  have h : PetersenPackedPin.project extra54 tgt = (0xfffffffffaeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b47_1
theorem hot54 : forcedConst extra54 tgt = false := by decide +kernel
def extra61 (r : Fin 64) : Fin 256 := (#[4,36,12,44,68,100,76,108,20,52,28,60,84,116,92,124,5,37,13,45,69,101,77,109,21,53,29,61,85,117,93,125,132,164,140,172,196,228,204,236,148,180,156,188,212,244,220,252,133,165,141,173,197,229,205,237,149,181,157,189,213,245,221,253] : Array (Fin 256))[r.val]?.getD 0
theorem small61 : NoAtMost i6 (PetersenPackedPin.project extra61 tgt) 5 := by
  have h : PetersenPackedPin.project extra61 tgt = (0xfffffffffaeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b47_1
theorem hot61 : forcedConst extra61 tgt = false := by decide +kernel
def extra62 (r : Fin 64) : Fin 256 := (#[2,10,34,42,130,138,162,170,18,26,50,58,146,154,178,186,3,11,35,43,131,139,163,171,19,27,51,59,147,155,179,187,66,74,98,106,194,202,226,234,82,90,114,122,210,218,242,250,67,75,99,107,195,203,227,235,83,91,115,123,211,219,243,251] : Array (Fin 256))[r.val]?.getD 0
theorem small62 : NoAtMost i6 (PetersenPackedPin.project extra62 tgt) 5 := by
  have h : PetersenPackedPin.project extra62 tgt = (0xfffffffffffff8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_2
theorem hot62 : forcedConst extra62 tgt = false := by decide +kernel
def extra69 (r : Fin 32) : Fin 256 := (#[0,64,16,80,128,192,144,208,4,68,20,84,132,196,148,212,8,72,24,88,136,200,152,216,12,76,28,92,140,204,156,220] : Array (Fin 256))[r.val]?.getD 0
theorem small69 : NoAtMost i5 (PetersenPackedPin.project extra69 tgt) 4 := by
  have h : PetersenPackedPin.project extra69 tgt = (0xfaeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra1020K12.b47_0
theorem hot69 : forcedConst extra69 tgt = false := by decide +kernel
def extra73 (r : Fin 64) : Fin 256 := (#[0,32,128,160,4,36,132,164,1,33,129,161,5,37,133,165,8,40,136,168,12,44,140,172,9,41,137,169,13,45,141,173,16,48,144,176,20,52,148,180,17,49,145,177,21,53,149,181,24,56,152,184,28,60,156,188,25,57,153,185,29,61,157,189] : Array (Fin 256))[r.val]?.getD 0
theorem small73 : NoAtMost i6 (PetersenPackedPin.project extra73 tgt) 5 := by
  have h : PetersenPackedPin.project extra73 tgt = (0xeeeeeecceaeaeac8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b119_0
theorem hot73 : forcedConst extra73 tgt = false := by decide +kernel
def extra74 (r : Fin 64) : Fin 256 := (#[64,65,96,97,192,193,224,225,68,69,100,101,196,197,228,229,72,73,104,105,200,201,232,233,76,77,108,109,204,205,236,237,80,81,112,113,208,209,240,241,84,85,116,117,212,213,244,245,88,89,120,121,216,217,248,249,92,93,124,125,220,221,252,253] : Array (Fin 256))[r.val]?.getD 0
theorem small74 : NoAtMost i6 (PetersenPackedPin.project extra74 tgt) 5 := by
  have h : PetersenPackedPin.project extra74 tgt = (0xfffffffffffff8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_2
theorem hot74 : forcedConst extra74 tgt = false := by decide +kernel
def extra75 (r : Fin 64) : Fin 256 := (#[2,10,34,42,130,138,162,170,18,26,50,58,146,154,178,186,3,11,35,43,131,139,163,171,19,27,51,59,147,155,179,187,6,14,38,46,134,142,166,174,22,30,54,62,150,158,182,190,7,15,39,47,135,143,167,175,23,31,55,63,151,159,183,191] : Array (Fin 256))[r.val]?.getD 0
theorem small75 : NoAtMost i6 (PetersenPackedPin.project extra75 tgt) 5 := by
  have h : PetersenPackedPin.project extra75 tgt = (0xfffffffffffff8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_2
theorem hot75 : forcedConst extra75 tgt = false := by decide +kernel
def extra76 (r : Fin 32) : Fin 256 := (#[0,32,8,40,64,96,72,104,16,48,24,56,80,112,88,120,1,33,9,41,65,97,73,105,17,49,25,57,81,113,89,121] : Array (Fin 256))[r.val]?.getD 0
theorem small76 : NoAtMost i5 (PetersenPackedPin.project extra76 tgt) 4 := by
  have h : PetersenPackedPin.project extra76 tgt = (0xfaeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra1020K12.b47_0
theorem hot76 : forcedConst extra76 tgt = false := by decide +kernel
def extra92 (r : Fin 64) : Fin 256 := (#[128,129,130,131,192,193,194,195,136,137,138,139,200,201,202,203,144,145,146,147,208,209,210,211,152,153,154,155,216,217,218,219,160,161,162,163,224,225,226,227,168,169,170,171,232,233,234,235,176,177,178,179,240,241,242,243,184,185,186,187,248,249,250,251] : Array (Fin 256))[r.val]?.getD 0
theorem small92 : NoAtMost i6 (PetersenPackedPin.project extra92 tgt) 5 := by
  have h : PetersenPackedPin.project extra92 tgt = (0xfffffffffffff8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_2
theorem hot92 : forcedConst extra92 tgt = false := by decide +kernel
def extra93 (r : Fin 64) : Fin 256 := (#[4,36,12,44,68,100,76,108,20,52,28,60,84,116,92,124,5,37,13,45,69,101,77,109,21,53,29,61,85,117,93,125,6,38,14,46,70,102,78,110,22,54,30,62,86,118,94,126,7,39,15,47,71,103,79,111,23,55,31,63,87,119,95,127] : Array (Fin 256))[r.val]?.getD 0
theorem small93 : NoAtMost i6 (PetersenPackedPin.project extra93 tgt) 5 := by
  have h : PetersenPackedPin.project extra93 tgt = (0xfffffffffaeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b47_1
theorem hot93 : forcedConst extra93 tgt = false := by decide +kernel
def extra97 (r : Fin 64) : Fin 256 := (#[32,36,34,38,96,100,98,102,48,52,50,54,112,116,114,118,33,37,35,39,97,101,99,103,49,53,51,55,113,117,115,119,160,164,162,166,224,228,226,230,176,180,178,182,240,244,242,246,161,165,163,167,225,229,227,231,177,181,179,183,241,245,243,247] : Array (Fin 256))[r.val]?.getD 0
theorem small97 : NoAtMost i6 (PetersenPackedPin.project extra97 tgt) 5 := by
  have h : PetersenPackedPin.project extra97 tgt = (0xfffffffffffff8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_2
theorem hot97 : forcedConst extra97 tgt = false := by decide +kernel
def extra99 (r : Fin 64) : Fin 256 := (#[64,65,96,97,192,193,224,225,68,69,100,101,196,197,228,229,66,67,98,99,194,195,226,227,70,71,102,103,198,199,230,231,80,81,112,113,208,209,240,241,84,85,116,117,212,213,244,245,82,83,114,115,210,211,242,243,86,87,118,119,214,215,246,247] : Array (Fin 256))[r.val]?.getD 0
theorem small99 : NoAtMost i6 (PetersenPackedPin.project extra99 tgt) 5 := by
  have h : PetersenPackedPin.project extra99 tgt = (0xfffffffffffff8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_2
theorem hot99 : forcedConst extra99 tgt = false := by decide +kernel
def extra107 (r : Fin 64) : Fin 256 := (#[64,65,96,97,192,193,224,225,68,69,100,101,196,197,228,229,66,67,98,99,194,195,226,227,70,71,102,103,198,199,230,231,72,73,104,105,200,201,232,233,76,77,108,109,204,205,236,237,74,75,106,107,202,203,234,235,78,79,110,111,206,207,238,239] : Array (Fin 256))[r.val]?.getD 0
theorem small107 : NoAtMost i6 (PetersenPackedPin.project extra107 tgt) 5 := by
  have h : PetersenPackedPin.project extra107 tgt = (0xfffffffffffff8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_2
theorem hot107 : forcedConst extra107 tgt = false := by decide +kernel
def extra108 (r : Fin 64) : Fin 256 := (#[16,18,17,19,48,50,49,51,24,26,25,27,56,58,57,59,20,22,21,23,52,54,53,55,28,30,29,31,60,62,61,63,144,146,145,147,176,178,177,179,152,154,153,155,184,186,185,187,148,150,149,151,180,182,181,183,156,158,157,159,188,190,189,191] : Array (Fin 256))[r.val]?.getD 0
theorem small108 : NoAtMost i6 (PetersenPackedPin.project extra108 tgt) 5 := by
  have h : PetersenPackedPin.project extra108 tgt = (0xfffffffffaeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b47_1
theorem hot108 : forcedConst extra108 tgt = false := by decide +kernel
def extra109 (r : Fin 64) : Fin 256 := (#[128,129,130,131,192,193,194,195,136,137,138,139,200,201,202,203,132,133,134,135,196,197,198,199,140,141,142,143,204,205,206,207,160,161,162,163,224,225,226,227,168,169,170,171,232,233,234,235,164,165,166,167,228,229,230,231,172,173,174,175,236,237,238,239] : Array (Fin 256))[r.val]?.getD 0
theorem small109 : NoAtMost i6 (PetersenPackedPin.project extra109 tgt) 5 := by
  have h : PetersenPackedPin.project extra109 tgt = (0xfffffffffffff8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_2
theorem hot109 : forcedConst extra109 tgt = false := by decide +kernel
def extra110 (r : Fin 64) : Fin 256 := (#[16,18,17,19,48,50,49,51,24,26,25,27,56,58,57,59,20,22,21,23,52,54,53,55,28,30,29,31,60,62,61,63,80,82,81,83,112,114,113,115,88,90,89,91,120,122,121,123,84,86,85,87,116,118,117,119,92,94,93,95,124,126,125,127] : Array (Fin 256))[r.val]?.getD 0
theorem small110 : NoAtMost i6 (PetersenPackedPin.project extra110 tgt) 5 := by
  have h : PetersenPackedPin.project extra110 tgt = (0xfffffffffaeaf8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b47_1
theorem hot110 : forcedConst extra110 tgt = false := by decide +kernel
def extra111 (r : Fin 32) : Fin 256 := (#[0,2,4,6,128,130,132,134,16,18,20,22,144,146,148,150,1,3,5,7,129,131,133,135,17,19,21,23,145,147,149,151] : Array (Fin 256))[r.val]?.getD 0
theorem small111 : NoAtMost i5 (PetersenPackedPin.project extra111 tgt) 4 := by
  have h : PetersenPackedPin.project extra111 tgt = (0xfaeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra1020K12.b47_0
theorem hot111 : forcedConst extra111 tgt = false := by decide +kernel
def extra115 (r : Fin 64) : Fin 256 := (#[0,2,64,66,8,10,72,74,1,3,65,67,9,11,73,75,4,6,68,70,12,14,76,78,5,7,69,71,13,15,77,79,16,18,80,82,24,26,88,90,17,19,81,83,25,27,89,91,20,22,84,86,28,30,92,94,21,23,85,87,29,31,93,95] : Array (Fin 256))[r.val]?.getD 0
theorem small115 : NoAtMost i6 (PetersenPackedPin.project extra115 tgt) 5 := by
  have h : PetersenPackedPin.project extra115 tgt = (0xeeeeeecceaeaeac8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b119_0
theorem hot115 : forcedConst extra115 tgt = false := by decide +kernel
def extra116 (r : Fin 64) : Fin 256 := (#[128,129,130,131,192,193,194,195,136,137,138,139,200,201,202,203,132,133,134,135,196,197,198,199,140,141,142,143,204,205,206,207,144,145,146,147,208,209,210,211,152,153,154,155,216,217,218,219,148,149,150,151,212,213,214,215,156,157,158,159,220,221,222,223] : Array (Fin 256))[r.val]?.getD 0
theorem small116 : NoAtMost i6 (PetersenPackedPin.project extra116 tgt) 5 := by
  have h : PetersenPackedPin.project extra116 tgt = (0xfffffffffffff8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_2
theorem hot116 : forcedConst extra116 tgt = false := by decide +kernel
def extra117 (r : Fin 64) : Fin 256 := (#[32,36,34,38,96,100,98,102,48,52,50,54,112,116,114,118,33,37,35,39,97,101,99,103,49,53,51,55,113,117,115,119,40,44,42,46,104,108,106,110,56,60,58,62,120,124,122,126,41,45,43,47,105,109,107,111,57,61,59,63,121,125,123,127] : Array (Fin 256))[r.val]?.getD 0
theorem small117 : NoAtMost i6 (PetersenPackedPin.project extra117 tgt) 5 := by
  have h : PetersenPackedPin.project extra117 tgt = (0xfffffffffffff8c8 : BitVec 64) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_2
theorem hot117 : forcedConst extra117 tgt = false := by decide +kernel
def extra118 (r : Fin 32) : Fin 256 := (#[0,2,1,3,32,34,33,35,8,10,9,11,40,42,41,43,4,6,5,7,36,38,37,39,12,14,13,15,44,46,45,47] : Array (Fin 256))[r.val]?.getD 0
theorem small118 : NoAtMost i5 (PetersenPackedPin.project extra118 tgt) 4 := by
  have h : PetersenPackedPin.project extra118 tgt = (0xfaeaf8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra1020K12.b47_0
theorem hot118 : forcedConst extra118 tgt = false := by decide +kernel
def extra141 (r : Fin 32) : Fin 256 := (#[0,128,32,160,8,136,40,168,4,132,36,164,12,140,44,172,16,144,48,176,24,152,56,184,20,148,52,180,28,156,60,188] : Array (Fin 256))[r.val]?.getD 0
theorem small141 : NoAtMost i5 (PetersenPackedPin.project extra141 tgt) 4 := by
  have h : PetersenPackedPin.project extra141 tgt = (0xeaeaeac8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra1020K12.b55_0
theorem hot141 : forcedConst extra141 tgt = false := by decide +kernel
def extra288 (r : Fin 32) : Fin 256 := (#[64,65,96,97,192,193,224,225,68,69,100,101,196,197,228,229,72,73,104,105,200,201,232,233,76,77,108,109,204,205,236,237] : Array (Fin 256))[r.val]?.getD 0
theorem small288 : NoAtMost i5 (PetersenPackedPin.project extra288 tgt) 4 := by
  have h : PetersenPackedPin.project extra288 tgt = (0xfffff8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_1
theorem hot288 : forcedConst extra288 tgt = false := by decide +kernel
def extra383 (r : Fin 32) : Fin 256 := (#[32,36,34,38,96,100,98,102,48,52,50,54,112,116,114,118,33,37,35,39,97,101,99,103,49,53,51,55,113,117,115,119] : Array (Fin 256))[r.val]?.getD 0
theorem small383 : NoAtMost i5 (PetersenPackedPin.project extra383 tgt) 4 := by
  have h : PetersenPackedPin.project extra383 tgt = (0xfffff8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_1
theorem hot383 : forcedConst extra383 tgt = false := by decide +kernel
def extra397 (r : Fin 32) : Fin 256 := (#[128,129,130,131,192,193,194,195,136,137,138,139,200,201,202,203,132,133,134,135,196,197,198,199,140,141,142,143,204,205,206,207] : Array (Fin 256))[r.val]?.getD 0
theorem small397 : NoAtMost i5 (PetersenPackedPin.project extra397 tgt) 4 := by
  have h : PetersenPackedPin.project extra397 tgt = (0xfffff8c8 : BitVec 32) := by decide +kernel
  rw [h]; exact Extra1020K12.b15_1
theorem hot397 : forcedConst extra397 tgt = false := by decide +kernel
end Orbits1020Cost12
