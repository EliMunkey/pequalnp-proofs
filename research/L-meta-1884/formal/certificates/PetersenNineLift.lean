import RSRange
import PetersenPairHints
open PetersenWordCost PetersenLayerCheck PetersenPackedPin PetersenVerifiedGroup PetersenFrontierSymmetry
open PetersenSignedBridge PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PetersenNineLift
open Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
def nine := graphTarget 9 [(0,1),(1,2),(2,3),(0,5),(1,6),(2,7),(3,8),(4,6),(6,8),(8,5),(5,7),(7,4)]
abbrev Hard (k : Nat) := NoAtMost (inputs 9) nine k
private theorem promote {u w : Nat} {r : Fin u→Fin w} {I L} {k : Nat} (q : rejects r I 0 [] L 1 = true) : rejects r I k [] L (k+1) = true := by
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp q; apply Bool.and_eq_true_iff.mpr; refine ⟨a,?_⟩
  have z := of_decide_eq_true b; apply decide_eq_true; simp only [List.length_nil,Nat.zero_add] at z ⊢; omega
def r2 (i : Fin 512) : Fin 1024 := (#[0,1,16,17,8,9,24,25,4,5,20,21,12,13,28,29,64,65,80,81,72,73,88,89,68,69,84,85,76,77,92,93,32,33,48,49,40,41,56,57,36,37,52,53,44,45,60,61,96,97,112,113,104,105,120,121,100,101,116,117,108,109,124,125,512,513,528,529,520,521,536,537,516,517,532,533,524,525,540,541,576,577,592,593,584,585,600,601,580,581,596,597,588,589,604,605,544,545,560,561,552,553,568,569,548,549,564,565,556,557,572,573,608,609,624,625,616,617,632,633,612,613,628,629,620,621,636,637,256,257,272,273,264,265,280,281,260,261,276,277,268,269,284,285,320,321,336,337,328,329,344,345,324,325,340,341,332,333,348,349,288,289,304,305,296,297,312,313,292,293,308,309,300,301,316,317,352,353,368,369,360,361,376,377,356,357,372,373,364,365,380,381,768,769,784,785,776,777,792,793,772,773,788,789,780,781,796,797,832,833,848,849,840,841,856,857,836,837,852,853,844,845,860,861,800,801,816,817,808,809,824,825,804,805,820,821,812,813,828,829,864,865,880,881,872,873,888,889,868,869,884,885,876,877,892,893,128,129,144,145,136,137,152,153,132,133,148,149,140,141,156,157,192,193,208,209,200,201,216,217,196,197,212,213,204,205,220,221,160,161,176,177,168,169,184,185,164,165,180,181,172,173,188,189,224,225,240,241,232,233,248,249,228,229,244,245,236,237,252,253,640,641,656,657,648,649,664,665,644,645,660,661,652,653,668,669,704,705,720,721,712,713,728,729,708,709,724,725,716,717,732,733,672,673,688,689,680,681,696,697,676,677,692,693,684,685,700,701,736,737,752,753,744,745,760,761,740,741,756,757,748,749,764,765,384,385,400,401,392,393,408,409,388,389,404,405,396,397,412,413,448,449,464,465,456,457,472,473,452,453,468,469,460,461,476,477,416,417,432,433,424,425,440,441,420,421,436,437,428,429,444,445,480,481,496,497,488,489,504,505,484,485,500,501,492,493,508,509,896,897,912,913,904,905,920,921,900,901,916,917,908,909,924,925,960,961,976,977,968,969,984,985,964,965,980,981,972,973,988,989,928,929,944,945,936,937,952,953,932,933,948,949,940,941,956,957,992,993,1008,1009,1000,1001,1016,1017,996,997,1012,1013,1004,1005,1020,1021] : Array (Fin 1024))[i.val]?.getD 0
private theorem target2 : PetersenPackedPin.project r2 tgt = nine := by decide +kernel
private theorem hot2 : forcedConst r2 tgt = false := by decide +kernel
def r3 (i : Fin 512) : Fin 1024 := (#[0,2,1,3,16,18,17,19,8,10,9,11,24,26,25,27,128,130,129,131,144,146,145,147,136,138,137,139,152,154,153,155,64,66,65,67,80,82,81,83,72,74,73,75,88,90,89,91,192,194,193,195,208,210,209,211,200,202,201,203,216,218,217,219,32,34,33,35,48,50,49,51,40,42,41,43,56,58,57,59,160,162,161,163,176,178,177,179,168,170,169,171,184,186,185,187,96,98,97,99,112,114,113,115,104,106,105,107,120,122,121,123,224,226,225,227,240,242,241,243,232,234,233,235,248,250,249,251,512,514,513,515,528,530,529,531,520,522,521,523,536,538,537,539,640,642,641,643,656,658,657,659,648,650,649,651,664,666,665,667,576,578,577,579,592,594,593,595,584,586,585,587,600,602,601,603,704,706,705,707,720,722,721,723,712,714,713,715,728,730,729,731,544,546,545,547,560,562,561,563,552,554,553,555,568,570,569,571,672,674,673,675,688,690,689,691,680,682,681,683,696,698,697,699,608,610,609,611,624,626,625,627,616,618,617,619,632,634,633,635,736,738,737,739,752,754,753,755,744,746,745,747,760,762,761,763,256,258,257,259,272,274,273,275,264,266,265,267,280,282,281,283,384,386,385,387,400,402,401,403,392,394,393,395,408,410,409,411,320,322,321,323,336,338,337,339,328,330,329,331,344,346,345,347,448,450,449,451,464,466,465,467,456,458,457,459,472,474,473,475,288,290,289,291,304,306,305,307,296,298,297,299,312,314,313,315,416,418,417,419,432,434,433,435,424,426,425,427,440,442,441,443,352,354,353,355,368,370,369,371,360,362,361,363,376,378,377,379,480,482,481,483,496,498,497,499,488,490,489,491,504,506,505,507,768,770,769,771,784,786,785,787,776,778,777,779,792,794,793,795,896,898,897,899,912,914,913,915,904,906,905,907,920,922,921,923,832,834,833,835,848,850,849,851,840,842,841,843,856,858,857,859,960,962,961,963,976,978,977,979,968,970,969,971,984,986,985,987,800,802,801,803,816,818,817,819,808,810,809,811,824,826,825,827,928,930,929,931,944,946,945,947,936,938,937,939,952,954,953,955,864,866,865,867,880,882,881,883,872,874,873,875,888,890,889,891,992,994,993,995,1008,1010,1009,1011,1000,1002,1001,1003,1016,1018,1017,1019] : Array (Fin 1024))[i.val]?.getD 0
private theorem target3 : PetersenPackedPin.project r3 tgt = nine := by decide +kernel
private theorem hot3 : forcedConst r3 tgt = false := by decide +kernel
def l1_0 : List (BitVec 1024) := (0x8888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888 : BitVec 1024)::primary
private theorem q1_0 : rejects r2 (inputs 9) 0 [] l1_0 1 = true := by decide +kernel
private theorem s1_0 {k : Nat} (low : Hard k) : Blocked tgt (k+1) l1_0 := by
  intro m le c; apply rejects_sound r2 (inputs 9) k tgt (target2 ▸ low) hot2 [] l1_0 (k+1) (promote q1_0) le
def l1_1 : List (BitVec 1024) := (0x2222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222 : BitVec 1024)::primary
private theorem q1_1 : rejects r2 (inputs 9) 0 [] l1_1 1 = true := by decide +kernel
private theorem s1_1 {k : Nat} (low : Hard k) : Blocked tgt (k+1) l1_1 := by
  intro m le c; apply rejects_sound r2 (inputs 9) k tgt (target2 ▸ low) hot2 [] l1_1 (k+1) (promote q1_1) le
def l1_2 : List (BitVec 1024) := (0x4444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444 : BitVec 1024)::primary
private theorem q1_2 : rejects r2 (inputs 9) 0 [] l1_2 1 = true := by decide +kernel
private theorem s1_2 {k : Nat} (low : Hard k) : Blocked tgt (k+1) l1_2 := by
  intro m le c; apply rejects_sound r2 (inputs 9) k tgt (target2 ▸ low) hot2 [] l1_2 (k+1) (promote q1_2) le
def l1_3 : List (BitVec 1024) := (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 1024)::primary
private theorem q1_3 : rejects r2 (inputs 9) 0 [] l1_3 1 = true := by decide +kernel
private theorem s1_3 {k : Nat} (low : Hard k) : Blocked tgt (k+1) l1_3 := by
  intro m le c; apply rejects_sound r2 (inputs 9) k tgt (target2 ▸ low) hot2 [] l1_3 (k+1) (promote q1_3) le
private theorem pair1 {k : Nat} (low : Hard k) : PetersenRootOrbit.DeadPair tgt (k+2) primary.toFinset (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 1024) (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc : BitVec 1024) := by
  apply PetersenPairHints.killed (nxt := #[l1_0,l1_1,l1_2,l1_3]) (hs := [4106,16405,4106,0,1031,2055,1031,3,7,2055,4106,1,7,16405,1031,2]) (by decide +kernel)
  intro V hv; change V ∈ [l1_0,l1_1,l1_2,l1_3] at hv; simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl
  · exact s1_0 low
  · exact s1_1 low
  · exact s1_2 low
  · exact s1_3 low
def l2_0 : List (BitVec 1024) := (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 : BitVec 1024)::primary
private theorem q2_0 : rejects r3 (inputs 9) 0 [] l2_0 1 = true := by decide +kernel
private theorem s2_0 {k : Nat} (low : Hard k) : Blocked tgt (k+1) l2_0 := by
  intro m le c; apply rejects_sound r3 (inputs 9) k tgt (target3 ▸ low) hot3 [] l2_0 (k+1) (promote q2_0) le
def l2_1 : List (BitVec 1024) := (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a : BitVec 1024)::primary
private theorem q2_1 : rejects r3 (inputs 9) 0 [] l2_1 1 = true := by decide +kernel
private theorem s2_1 {k : Nat} (low : Hard k) : Blocked tgt (k+1) l2_1 := by
  intro m le c; apply rejects_sound r3 (inputs 9) k tgt (target3 ▸ low) hot3 [] l2_1 (k+1) (promote q2_1) le
def l2_2 : List (BitVec 1024) := (0x5050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050 : BitVec 1024)::primary
private theorem q2_2 : rejects r3 (inputs 9) 0 [] l2_2 1 = true := by decide +kernel
private theorem s2_2 {k : Nat} (low : Hard k) : Blocked tgt (k+1) l2_2 := by
  intro m le c; apply rejects_sound r3 (inputs 9) k tgt (target3 ▸ low) hot3 [] l2_2 (k+1) (promote q2_2) le
def l2_3 : List (BitVec 1024) := (0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa : BitVec 1024)::primary
private theorem q2_3 : rejects r3 (inputs 9) 0 [] l2_3 1 = true := by decide +kernel
private theorem s2_3 {k : Nat} (low : Hard k) : Blocked tgt (k+1) l2_3 := by
  intro m le c; apply rejects_sound r3 (inputs 9) k tgt (target3 ▸ low) hot3 [] l2_3 (k+1) (promote q2_3) le
private theorem pair2 {k : Nat} (low : Hard k) : PetersenRootOrbit.DeadPair tgt (k+2) primary.toFinset (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 1024) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 1024) := by
  apply PetersenPairHints.killed (nxt := #[l2_0,l2_1,l2_2,l2_3]) (hs := [2055,2055,2058,0,9232,20505,9233,3,2058,20505,2058,1,2055,2055,9233,2]) (by decide +kernel)
  intro V hv; change V ∈ [l2_0,l2_1,l2_2,l2_3] at hv; simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl
  · exact s2_0 low
  · exact s2_1 low
  · exact s2_2 low
  · exact s2_3 low
theorem closure {k : Nat} (low : Hard k) : Blocked tgt (k+2) primary := by
  rw [←tgt_eq,←raw_eq]; apply PetersenRootOrbit.two_pairs; all_goals rw [tgt_eq,raw_eq]
  · exact pair1 low
  · exact pair2 low
theorem signed {k : Nat} (low : Hard k) : NoAtMost (inputs 10) PetersenPackedRoot.target (k+2) := by
  rw [origin_eq,raw_eq]
  apply PetersenSignedDemand.lower (by decide) _ (by rfl) _ probes (by decide +kernel) (closure low)
  · intro a ha; unfold primary at ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · constructor
    · intro eq; have h := congrFun eq (3 : Fin 1024); change true = false at h; contradiction
    · intro eq; have h := congrFun eq (0 : Fin 1024); change false = true at h; contradiction
theorem public_lower {k : Nat} (low : Hard k) (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (fan : FanInTwo C) (computes : ∀ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = PetersenTarget x) : k+3 ≤ C.size := by
  obtain ⟨W,run,out⟩ := signed_realization C σ u fan; rw [funext computes] at out; by_contra h
  exact PetersenPackedRoot.signed_of_words (signed low) _ (by
    have le : (C.gates.filter paid).length ≤ C.gates.length := List.length_filter_le ..
    change ¬k+3 ≤ C.gates.length at h; omega) W run out
#print axioms signed
#print axioms public_lower
end PetersenNineLift
