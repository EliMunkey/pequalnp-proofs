import PetersenElevenAntichain
import PetersenElevenCofactors
open PetersenAntichain PetersenFrontier PetersenWordCost PetersenAntiStep PetersenElevenAntichain PetersenPhysicalWords PetersenFrontierSymmetry
open PetersenSignedBridge PetersenPhysicalRowGroup
namespace PetersenElevenCensus
local notation "B" => BitVec 38
set_option maxHeartbeats 0
set_option maxRecDepth 120000
def orbit : List ((B × Bool) × Fin 12 × (B × Bool)) := [((0x1,false),0,(0x1,false)),((0x1,true),0,(0x1,true)),((0x2,false),0,(0x2,false)),((0x2,true),0,(0x2,true)),((0xc,false),0,(0xc,false)),((0xc,true),0,(0xc,true)),((0x10,false),4,(0x1,false)),((0x10,true),4,(0x1,true)),((0x20,false),4,(0x2,false)),((0x20,true),4,(0x2,true)),((0x40,false),5,(0x1,false)),((0x40,true),5,(0x1,true)),((0x100,false),2,(0x2,false)),((0x100,true),2,(0x2,true)),((0x3000,false),1,(0xc,false)),((0x3000,true),1,(0xc,true)),((0x8000,false),5,(0x2,false)),((0x8000,true),5,(0x2,true)),((0x180000,false),8,(0xc,false)),((0x180000,true),8,(0xc,true)),((0x400000,false),7,(0x2,false)),((0x400000,true),7,(0x2,true)),((0x1800000,false),2,(0xc,false)),((0x1800000,true),2,(0xc,true)),((0x8120008,false),0,(0x8120008,false)),((0x8120008,true),0,(0x8120008,true)),((0x10000000,false),6,(0x2,false)),((0x10000000,true),6,(0x2,true)),((0x40094424,false),0,(0x40094424,false)),((0x40094424,true),0,(0x40094424,true)),((0x5c3f4cbc,false),0,(0x5c3f4cbc,false)),((0x5c3f4cbc,true),0,(0x5c3f4cbc,true)),((0x685bccec,false),0,(0x685bccec,false)),((0x685bccec,true),0,(0x685bccec,true)),((0x74648cf0,false),0,(0x74648cf0,false)),((0x74648cf0,true),0,(0x74648cf0,true)),((0x80850d00,false),6,(0x40094424,false)),((0x80850d00,true),6,(0x40094424,true)),((0x101020200,false),6,(0x8120008,false)),((0x101020200,true),6,(0x8120008,true)),((0x180000000,false),3,(0xc,false)),((0x180000000,true),3,(0xc,true)),((0x195a70fb0,false),7,(0x685bccec,false)),((0x195a70fb0,true),7,(0x685bccec,true)),((0x1c99f4f2c,false),0,(0x1c99f4f2c,false)),((0x1c99f4f2c,true),0,(0x1c99f4f2c,true)),((0x1e1c78fc0,false),6,(0x685bccec,false)),((0x1e1c78fc0,true),6,(0x685bccec,true)),((0x20405d000,false),1,(0x40094424,false)),((0x20405d000,true),1,(0x40094424,true)),((0x402022000,false),1,(0x8120008,false)),((0x402022000,true),1,(0x8120008,true)),((0x600000000,false),9,(0xc,false)),((0x600000000,true),9,(0xc,true)),((0x61627f8b0,false),1,(0x685bccec,false)),((0x61627f8b0,true),1,(0x685bccec,true)),((0x64e1ff42c,false),10,(0x1c99f4f2c,false)),((0x64e1ff42c,true),10,(0x1c99f4f2c,true)),((0x66647fcc0,false),1,(0x5c3f4cbc,false)),((0x66647fcc0,true),1,(0x5c3f4cbc,true)),((0x78787ff00,false),1,(0x1c99f4f2c,false)),((0x78787ff00,true),1,(0x1c99f4f2c,true)),((0x84c1b45af,false),10,(0x685bccec,false)),((0x84c1b45af,true),10,(0x685bccec,true)),((0x8542449b3,false),5,(0x74648cf0,false)),((0x8542449b3,true),5,(0x74648cf0,true)),((0x86440cdc3,false),4,(0x74648cf0,false)),((0x86440cdc3,true),4,(0x74648cf0,true)),((0x9c5874f83,false),6,(0x5c3f4cbc,false)),((0x9c5874f83,true),6,(0x5c3f4cbc,true)),((0xe4607f183,false),11,(0x685bccec,false)),((0xe4607f183,true),11,(0x685bccec,true)),((0x1020201806,false),4,(0x40094424,false)),((0x1020201806,true),4,(0x40094424,true)),((0x1804e80000,false),2,(0x40094424,false)),((0x1804e80000,true),2,(0x40094424,true)),((0x1af0000000,false),3,(0x40094424,false)),((0x1af0000000,true),3,(0x40094424,true)),((0x1af4eddda7,false),0,(0x1af4eddda7,false)),((0x1af4edddb6,false),4,(0x1af4eddda7,false)),((0x1af4eddde6,false),5,(0x1af4eddda7,false)),((0x1afcffddae,false),0,(0x1afcffddae,false)),((0x1afcffddae,true),0,(0x1afcffddae,true)),((0x1bf5efdfa6,false),6,(0x1afcffddae,false)),((0x1bf5efdfa6,true),6,(0x1afcffddae,true)),((0x1ef6effda6,false),1,(0x1afcffddae,false)),((0x1ef6effda6,true),1,(0x1afcffddae,true)),((0x2000002208,false),4,(0x8120008,false)),((0x2000002208,true),4,(0x8120008,true)),((0x2003100000,false),2,(0x8120008,false)),((0x2003100000,true),2,(0x8120008,true)),((0x2508000000,false),3,(0x8120008,false)),((0x2508000000,true),3,(0x8120008,true)),((0x251f362af9,false),0,(0x251f362af9,false)),((0x251f362af9,true),0,(0x251f362af9,true)),((0x254b1b667d,false),0,(0x254b1b667d,false)),((0x254b1b667d,true),0,(0x254b1b667d,true)),((0x256b52aed9,false),1,(0x251f362af9,false)),((0x256b52aed9,true),1,(0x251f362af9,true)),((0x258b972f59,false),6,(0x254b1b667d,false)),((0x258b972f59,true),6,(0x254b1b667d,true)),((0x270f17f259,false),1,(0x254b1b667d,false)),((0x270f17f259,true),1,(0x254b1b667d,true)),((0x2d4f1263db,false),4,(0x251f362af9,false)),((0x2d4f1263db,true),4,(0x251f362af9,true)),((0x3034243abe,false),5,(0x685bccec,false)),((0x3034243abe,true),5,(0x685bccec,true)),((0x306060bece,false),4,(0x685bccec,false)),((0x306060bece,true),4,(0x685bccec,true)),((0x30683b7e2e,false),0,(0x30683b7e2e,false)),((0x30683b7e2e,true),0,(0x30683b7e2e,true)),((0x31a1a73f0e,false),0,(0x31a1a73f0e,false)),((0x31a1a73f0e,true),0,(0x31a1a73f0e,true)),((0x352b323a5f,false),4,(0x254b1b667d,false)),((0x352b323a5f,true),4,(0x254b1b667d,true)),((0x362627fa0e,false),1,(0x30683b7e2e,false)),((0x362627fa0e,true),1,(0x30683b7e2e,true)),((0x3817fc08b0,false),2,(0x685bccec,false)),((0x3817fc08b0,true),2,(0x685bccec,true)),((0x3827f83a0e,false),2,(0x1c99f4f2c,false)),((0x3827f83a0e,true),2,(0x1c99f4f2c,true)),((0x3847f84183,false),8,(0x685bccec,false)),((0x3847f84183,true),8,(0x685bccec,true)),((0x384ffb442c,false),8,(0x30683b7e2e,false)),((0x384ffb442c,true),8,(0x30683b7e2e,true)),((0x3864207b8f,false),4,(0x5c3f4cbc,false)),((0x3864207b8f,true),4,(0x5c3f4cbc,true)),((0x3867f88cc0,false),2,(0x5c3f4cbc,false)),((0x3867f88cc0,true),2,(0x5c3f4cbc,true)),((0x3987ff0f00,false),2,(0x30683b7e2e,false)),((0x3987ff0f00,true),2,(0x30683b7e2e,true)),((0x3af4edffae,false),4,(0x1afcffddae,false)),((0x3af4edffae,true),4,(0x1afcffddae,true)),((0x3af7fddda6,false),2,(0x1afcffddae,false)),((0x3af7fddda6,true),2,(0x1afcffddae,true)),((0x3d0ffa2259,false),2,(0x254b1b667d,false)),((0x3d0ffa2259,true),2,(0x254b1b667d,true)),((0x3e07fff000,false),5,(0x31a1a73f0e,false)),((0x3e07fff000,true),5,(0x31a1a73f0e,true)),((0x3ff81b442c,false),4,(0x31a1a73f0e,false)),((0x3ff81b442c,true),4,(0x31a1a73f0e,true)),((0x3ff8203a0e,false),3,(0x1c99f4f2c,false)),((0x3ff8203a0e,true),3,(0x1c99f4f2c,true)),((0x3ff8408cc0,false),3,(0x685bccec,false)),((0x3ff8408cc0,true),3,(0x685bccec,true)),((0x3ff9870f00,false),3,(0x30683b7e2e,false)),((0x3ff9870f00,true),3,(0x30683b7e2e,true)),((0x3ffb122259,false),3,(0x254b1b667d,false)),((0x3ffb122259,true),3,(0x254b1b667d,true)),((0x3ffc004183,false),9,(0x685bccec,false)),((0x3ffc004183,true),9,(0x685bccec,true)),((0x3ffc2408b0,false),3,(0x5c3f4cbc,false)),((0x3ffc2408b0,true),3,(0x5c3f4cbc,true)),((0x3ffceddda6,false),3,(0x1afcffddae,false)),((0x3ffceddda6,true),3,(0x1afcffddae,true)),((0x3ffe07f000,false),9,(0x30683b7e2e,false)),((0x3ffe07f000,true),9,(0x30683b7e2e,true)),((0x3ffff80000,false),8,(0x1c99f4f2c,false)),((0x3ffff80000,true),8,(0x1c99f4f2c,true))]
def reps : List (B × Bool) := [(0x1,false),(0x1,true),(0x2,false),(0x2,true),(0xc,false),(0xc,true),(0x8120008,false),(0x8120008,true),(0x40094424,false),(0x40094424,true),(0x5c3f4cbc,false),(0x5c3f4cbc,true),(0x685bccec,false),(0x685bccec,true),(0x74648cf0,false),(0x74648cf0,true),(0x1c99f4f2c,false),(0x1c99f4f2c,true),(0x1af4eddda7,false),(0x1afcffddae,false),(0x1afcffddae,true),(0x251f362af9,false),(0x251f362af9,true),(0x254b1b667d,false),(0x254b1b667d,true),(0x30683b7e2e,false),(0x30683b7e2e,true),(0x31a1a73f0e,false),(0x31a1a73f0e,true)]
def remaining : List (B × Bool) := [(0x2,true),(0xc,true),(0x5c3f4cbc,false),(0x5c3f4cbc,true),(0x685bccec,false),(0x685bccec,true),(0x74648cf0,false),(0x74648cf0,true),(0x1c99f4f2c,false),(0x1c99f4f2c,true),(0x251f362af9,false),(0x254b1b667d,false),(0x30683b7e2e,false),(0x30683b7e2e,true),(0x31a1a73f0e,false),(0x31a1a73f0e,true)]
def killed : List (B × Bool) := [(0x1,false),(0x1,true),(0x2,false),(0xc,false),(0x8120008,false),(0x8120008,true),(0x40094424,false),(0x40094424,true),(0x1af4eddda7,false),(0x1afcffddae,false),(0x1afcffddae,true),(0x251f362af9,true),(0x254b1b667d,true)]
abbrev Debt (v : B × Bool) := PetersenAntiStep.Blocked PetersenEleven.sources target 17 (state v)
private theorem missing (b : Bool) : target ∉ (if b then PetersenEleven.sources else input).toFinset := by cases b <;> decide +kernel
private theorem classifies (b : Bool) : (let L := if b then PetersenEleven.sources else input; (PetersenAntiStep.moves PetersenEleven.sources L target negatives (17+2-L.toFinset.card)).all (fun V => orbit.any fun e => V == state e.1)) = true := by cases b <;> decide +kernel
private theorem transport : orbit.all (fun (v,i,r) => ((act (group i).row v.1, v.2) == r) && reps.contains r) = true := by decide +kernel
private theorem partition : reps.all (fun v => remaining.contains v || killed.contains v) = true := by decide +kernel
private def row0 : Fin 24 → Fin 38 := ![2,19,23,1,8,12,16,14,5,21,18,26,22,10,15,11,7,36,31,35,33,28,29,30]
private theorem target0 : PetersenPackedPin.project row0 target = PetersenNineData.label := by decide +kernel
private def row1 : Fin 24 → Fin 38 := ![5,28,33,2,12,19,26,21,4,27,25,37,31,18,23,17,9,30,15,29,22,6,10,11]
private theorem target1 : PetersenPackedPin.project row1 target = PetersenNineData.label := by decide +kernel
private def row2 : Fin 24 → Fin 38 := ![4,28,31,0,8,6,11,7,5,27,10,30,33,18,15,17,14,37,23,35,22,19,25,26]
private theorem target2 : PetersenPackedPin.project row2 target = PetersenNineData.label := by decide +kernel
private def row3 : Fin 24 → Fin 38 := ![0,8,31,4,28,6,30,7,1,9,29,11,23,35,22,37,21,17,33,18,15,12,25,26]
private theorem target3 : PetersenPackedPin.project row3 target = PetersenNineData.label := by decide +kernel
private theorem kill0 (nine : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label 15) : Debt (0x1,false) := by
  intro m hm credit tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have low : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis (PetersenPackedPin.project row0 target) 15 := target0 ▸ nine
  exact PetersenPositiveCheck.sound row0 low (by decide) (p := []) (L := state (0x1,false)) (fuel := 17) (by decide +kernel) hm plain
private theorem kill1 (nine : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label 15) : Debt (0x1,true) := by
  intro m hm credit tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have low : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis (PetersenPackedPin.project row0 target) 15 := target0 ▸ nine
  exact PetersenPositiveCheck.sound row0 low (by decide) (p := []) (L := state (0x1,true)) (fuel := 17) (by decide +kernel) hm plain
private theorem kill2 (nine : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label 15) : Debt (0x2,false) := by
  intro m hm credit tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have low : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis (PetersenPackedPin.project row1 target) 15 := target1 ▸ nine
  exact PetersenPositiveCheck.sound row1 low (by decide) (p := []) (L := state (0x2,false)) (fuel := 17) (by decide +kernel) hm plain
private theorem kill3 (nine : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label 15) : Debt (0xc,false) := by
  intro m hm credit tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have low : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis (PetersenPackedPin.project row2 target) 15 := target2 ▸ nine
  exact PetersenPositiveCheck.sound row2 low (by decide) (p := []) (L := state (0xc,false)) (fuel := 17) (by decide +kernel) hm plain
private theorem kill4 (nine : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label 15) : Debt (0x8120008,false) := by
  intro m hm credit tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have low : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis (PetersenPackedPin.project row0 target) 15 := target0 ▸ nine
  exact PetersenPositiveCheck.sound row0 low (by decide) (p := []) (L := state (0x8120008,false)) (fuel := 17) (by decide +kernel) hm plain
private theorem kill5 (nine : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label 15) : Debt (0x8120008,true) := by
  intro m hm credit tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have low : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis (PetersenPackedPin.project row0 target) 15 := target0 ▸ nine
  exact PetersenPositiveCheck.sound row0 low (by decide) (p := []) (L := state (0x8120008,true)) (fuel := 17) (by decide +kernel) hm plain
private theorem kill6 (nine : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label 15) : Debt (0x40094424,false) := by
  intro m hm credit tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have low : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis (PetersenPackedPin.project row3 target) 15 := target3 ▸ nine
  exact PetersenPositiveCheck.sound row3 low (by decide) (p := []) (L := state (0x40094424,false)) (fuel := 17) (by decide +kernel) hm plain
private theorem kill7 (nine : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label 15) : Debt (0x40094424,true) := by
  intro m hm credit tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have low : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis (PetersenPackedPin.project row0 target) 15 := target0 ▸ nine
  exact PetersenPositiveCheck.sound row0 low (by decide) (p := []) (L := state (0x40094424,true)) (fuel := 17) (by decide +kernel) hm plain
private theorem kill8 (nine : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label 15) : Debt (0x1af4eddda7,false) := by
  intro m hm credit tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have low : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis (PetersenPackedPin.project row0 target) 15 := target0 ▸ nine
  exact PetersenPositiveCheck.sound row0 low (by decide) (p := []) (L := state (0x1af4eddda7,false)) (fuel := 17) (by decide +kernel) hm plain
private theorem kill9 (nine : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label 15) : Debt (0x1afcffddae,false) := by
  intro m hm credit tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have low : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis (PetersenPackedPin.project row0 target) 15 := target0 ▸ nine
  exact PetersenPositiveCheck.sound row0 low (by decide) (p := []) (L := state (0x1afcffddae,false)) (fuel := 17) (by decide +kernel) hm plain
private theorem kill10 (nine : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label 15) : Debt (0x1afcffddae,true) := by
  intro m hm credit tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have low : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis (PetersenPackedPin.project row0 target) 15 := target0 ▸ nine
  exact PetersenPositiveCheck.sound row0 low (by decide) (p := []) (L := state (0x1afcffddae,true)) (fuel := 17) (by decide +kernel) hm plain
private theorem kill11 (nine : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label 15) : Debt (0x251f362af9,true) := by
  intro m hm credit tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have low : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis (PetersenPackedPin.project row0 target) 15 := target0 ▸ nine
  exact PetersenPositiveCheck.sound row0 low (by decide) (p := []) (L := state (0x251f362af9,true)) (fuel := 17) (by decide +kernel) hm plain
private theorem kill12 (nine : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label 15) : Debt (0x254b1b667d,true) := by
  intro m hm credit tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have low : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis (PetersenPackedPin.project row0 target) 15 := target0 ▸ nine
  exact PetersenPositiveCheck.sound row0 low (by decide) (p := []) (L := state (0x254b1b667d,true)) (fuel := 17) (by decide +kernel) hm plain
private theorem allKills (nine : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label 15) : ∀ c∈killed, Debt c := by
  intro c h; unfold killed at h; simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact kill0 nine
  · exact kill1 nine
  · exact kill2 nine
  · exact kill3 nine
  · exact kill4 nine
  · exact kill5 nine
  · exact kill6 nine
  · exact kill7 nine
  · exact kill8 nine
  · exact kill9 nine
  · exact kill10 nine
  · exact kill11 nine
  · exact kill12 nine
theorem close_small (nine : PetersenPhysicalProjection.NoPhysical PetersenNineProjected.basis PetersenNineData.label 15) (done : ∀ c∈remaining, Debt c) : ∀ W, Direct rails 18 W → PetersenTarget ∉ W := by
  intro W w out; obtain ⟨b,m,le,c,tail⟩ := PetersenElevenAntichain.normalized w out
  apply PetersenAntiStep.split negatives (missing b) _ m le c tail
  intro V mv; obtain ⟨⟨v,i,r⟩,mem,eq⟩ := List.any_eq_true.mp (List.all_eq_true.mp (classifies b) V mv)
  have valid := Bool.and_eq_true_iff.mp (List.all_eq_true.mp transport (v,i,r) mem)
  have re := List.contains_iff_mem.mp valid.2
  have rr : Debt r := by
    rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp partition r re) with hr|hk
    · exact done r (List.contains_iff_mem.mp hr)
    · exact allKills nine r (List.contains_iff_mem.mp hk)
  have q := beq_iff_eq.mp eq; subst V
  apply PetersenAntiOrbit.blocked (group i).row (by rw [target_eq,target_act]) (src_map _) _ rr
  rw [map_state,beq_iff_eq.mp valid.1]
theorem close (nine : PetersenElevenCofactors.suffix) (done : ∀ c∈remaining, Debt c) : ∀ W, Direct rails 18 W → PetersenTarget ∉ W := close_small (PetersenNineProjected.small nine) done
theorem remaining_count : remaining.length = 16 := by decide
#print axioms close
end PetersenElevenCensus
