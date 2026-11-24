import PetersenFrontierSymmetry
open PetersenFrontierSymmetry PetersenWordCost
namespace PetersenVerifiedGroup
abbrev V := Fin 10
def E : List (V × V) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def code (i j : V) : Bool := (![50,69,138,276,521,385,770,548,104,208] : Fin 10 → Nat) i |>.testBit j.val
theorem code_spec (i j : V) : Adj E i j ↔ code i j = true := by unfold Adj; revert i j; decide
structure Aut where
  toEquiv : V ≃ V
  correct : ∀ i j, code (toEquiv i) (toEquiv j) = code i j

theorem stable_target (a : Aut) : act (vertexRows a.toEquiv) (graphWord E) = graphWord E := by
  apply graph_invariant
  intro i j
  rw [code_spec,code_spec,a.correct]


private def p0 : Aut := by
  let f : V → V := ![0,1,2,3,4,5,6,7,8,9]
  let g : V → V := ![0,1,2,3,4,5,6,7,8,9]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p1 : Aut := by
  let f : V → V := ![0,1,2,7,5,4,6,3,9,8]
  let g : V → V := ![0,1,2,7,5,4,6,3,9,8]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p2 : Aut := by
  let f : V → V := ![0,1,6,8,5,4,2,9,3,7]
  let g : V → V := ![0,1,6,8,5,4,2,9,3,7]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p3 : Aut := by
  let f : V → V := ![0,1,6,9,4,5,2,8,7,3]
  let g : V → V := ![0,1,6,9,4,5,2,8,7,3]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p4 : Aut := by
  let f : V → V := ![0,4,3,2,1,5,9,8,7,6]
  let g : V → V := ![0,4,3,2,1,5,9,8,7,6]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p5 : Aut := by
  let f : V → V := ![0,4,3,8,5,1,9,2,6,7]
  let g : V → V := ![0,5,7,2,1,4,8,9,3,6]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p6 : Aut := by
  let f : V → V := ![0,4,9,6,1,5,3,7,8,2]
  let g : V → V := ![0,4,9,6,1,5,3,7,8,2]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p7 : Aut := by
  let f : V → V := ![0,4,9,7,5,1,3,6,2,8]
  let g : V → V := ![0,5,8,6,1,4,7,3,9,2]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p8 : Aut := by
  let f : V → V := ![0,5,7,2,1,4,8,9,3,6]
  let g : V → V := ![0,4,3,8,5,1,9,2,6,7]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p9 : Aut := by
  let f : V → V := ![0,5,7,9,4,1,8,2,6,3]
  let g : V → V := ![0,5,7,9,4,1,8,2,6,3]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p10 : Aut := by
  let f : V → V := ![0,5,8,3,4,1,7,6,2,9]
  let g : V → V := ![0,5,8,3,4,1,7,6,2,9]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p11 : Aut := by
  let f : V → V := ![0,5,8,6,1,4,7,3,9,2]
  let g : V → V := ![0,4,9,7,5,1,3,6,2,8]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p12 : Aut := by
  let f : V → V := ![1,0,4,3,2,6,5,9,8,7]
  let g : V → V := ![1,0,4,3,2,6,5,9,8,7]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p13 : Aut := by
  let f : V → V := ![1,0,4,9,6,2,5,3,7,8]
  let g : V → V := ![1,0,5,7,2,6,4,8,9,3]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p14 : Aut := by
  let f : V → V := ![1,0,5,7,2,6,4,8,9,3]
  let g : V → V := ![1,0,4,9,6,2,5,3,7,8]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p15 : Aut := by
  let f : V → V := ![1,0,5,8,6,2,4,7,3,9]
  let g : V → V := ![1,0,5,8,6,2,4,7,3,9]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p16 : Aut := by
  let f : V → V := ![1,2,3,4,0,6,7,8,9,5]
  let g : V → V := ![4,0,1,2,3,9,5,6,7,8]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p17 : Aut := by
  let f : V → V := ![1,2,3,8,6,0,7,4,5,9]
  let g : V → V := ![5,0,1,2,7,8,4,6,3,9]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p18 : Aut := by
  let f : V → V := ![1,2,7,5,0,6,3,9,8,4]
  let g : V → V := ![4,0,1,6,9,3,5,2,8,7]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p19 : Aut := by
  let f : V → V := ![1,2,7,9,6,0,3,5,4,8]
  let g : V → V := ![5,0,1,6,8,7,4,2,9,3]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p20 : Aut := by
  let f : V → V := ![1,6,8,3,2,0,9,5,4,7]
  let g : V → V := ![5,0,4,3,8,7,1,9,2,6]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p21 : Aut := by
  let f : V → V := ![1,6,8,5,0,2,9,3,7,4]
  let g : V → V := ![4,0,5,7,9,3,1,8,2,6]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p22 : Aut := by
  let f : V → V := ![1,6,9,4,0,2,8,7,3,5]
  let g : V → V := ![4,0,5,8,3,9,1,7,6,2]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p23 : Aut := by
  let f : V → V := ![1,6,9,7,2,0,8,4,5,3]
  let g : V → V := ![5,0,4,9,7,8,1,3,6,2]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p24 : Aut := by
  let f : V → V := ![2,1,0,4,3,7,6,5,9,8]
  let g : V → V := ![2,1,0,4,3,7,6,5,9,8]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p25 : Aut := by
  let f : V → V := ![2,1,0,5,7,3,6,4,8,9]
  let g : V → V := ![2,1,0,5,7,3,6,4,8,9]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p26 : Aut := by
  let f : V → V := ![2,1,6,8,3,7,0,9,5,4]
  let g : V → V := ![6,1,0,4,9,8,2,5,3,7]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p27 : Aut := by
  let f : V → V := ![2,1,6,9,7,3,0,8,4,5]
  let g : V → V := ![6,1,0,5,8,9,2,4,7,3]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p28 : Aut := by
  let f : V → V := ![2,3,4,0,1,7,8,9,5,6]
  let g : V → V := ![3,4,0,1,2,8,9,5,6,7]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p29 : Aut := by
  let f : V → V := ![2,3,4,9,7,1,8,0,6,5]
  let g : V → V := ![7,5,0,1,2,9,8,4,6,3]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p30 : Aut := by
  let f : V → V := ![2,3,8,5,7,1,4,6,0,9]
  let g : V → V := ![8,5,0,1,6,3,7,4,2,9]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p31 : Aut := by
  let f : V → V := ![2,3,8,6,1,7,4,5,9,0]
  let g : V → V := ![9,4,0,1,6,7,3,5,2,8]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p32 : Aut := by
  let f : V → V := ![2,7,5,0,1,3,9,8,4,6]
  let g : V → V := ![3,4,0,5,8,2,9,1,7,6]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p33 : Aut := by
  let f : V → V := ![2,7,5,8,3,1,9,0,6,4]
  let g : V → V := ![7,5,0,4,9,2,8,1,3,6]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p34 : Aut := by
  let f : V → V := ![2,7,9,4,3,1,5,6,0,8]
  let g : V → V := ![8,5,0,4,3,6,7,1,9,2]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p35 : Aut := by
  let f : V → V := ![2,7,9,6,1,3,5,4,8,0]
  let g : V → V := ![9,4,0,5,7,6,3,1,8,2]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p36 : Aut := by
  let f : V → V := ![3,2,1,0,4,8,7,6,5,9]
  let g : V → V := ![3,2,1,0,4,8,7,6,5,9]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p37 : Aut := by
  let f : V → V := ![3,2,1,6,8,4,7,0,9,5]
  let g : V → V := ![7,2,1,0,5,9,3,6,4,8]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p38 : Aut := by
  let f : V → V := ![3,2,7,5,8,4,1,9,0,6]
  let g : V → V := ![8,6,1,0,5,3,9,2,4,7]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p39 : Aut := by
  let f : V → V := ![3,2,7,9,4,8,1,5,6,0]
  let g : V → V := ![9,6,1,0,4,7,8,2,5,3]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p40 : Aut := by
  let f : V → V := ![3,4,0,1,2,8,9,5,6,7]
  let g : V → V := ![2,3,4,0,1,7,8,9,5,6]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p41 : Aut := by
  let f : V → V := ![3,4,0,5,8,2,9,1,7,6]
  let g : V → V := ![2,7,5,0,1,3,9,8,4,6]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p42 : Aut := by
  let f : V → V := ![3,4,9,6,8,2,0,7,1,5]
  let g : V → V := ![6,8,5,0,1,9,3,7,4,2]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p43 : Aut := by
  let f : V → V := ![3,4,9,7,2,8,0,6,5,1]
  let g : V → V := ![6,9,4,0,1,8,7,3,5,2]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p44 : Aut := by
  let f : V → V := ![3,8,5,0,4,2,6,7,1,9]
  let g : V → V := ![3,8,5,0,4,2,6,7,1,9]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p45 : Aut := by
  let f : V → V := ![3,8,5,7,2,4,6,0,9,1]
  let g : V → V := ![7,9,4,0,5,2,6,3,1,8]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p46 : Aut := by
  let f : V → V := ![3,8,6,1,2,4,5,9,0,7]
  let g : V → V := ![8,3,4,0,5,6,2,9,1,7]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p47 : Aut := by
  let f : V → V := ![3,8,6,9,4,2,5,1,7,0]
  let g : V → V := ![9,7,5,0,4,6,2,8,1,3]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p48 : Aut := by
  let f : V → V := ![4,0,1,2,3,9,5,6,7,8]
  let g : V → V := ![1,2,3,4,0,6,7,8,9,5]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p49 : Aut := by
  let f : V → V := ![4,0,1,6,9,3,5,2,8,7]
  let g : V → V := ![1,2,7,5,0,6,3,9,8,4]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p50 : Aut := by
  let f : V → V := ![4,0,5,7,9,3,1,8,2,6]
  let g : V → V := ![1,6,8,5,0,2,9,3,7,4]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p51 : Aut := by
  let f : V → V := ![4,0,5,8,3,9,1,7,6,2]
  let g : V → V := ![1,6,9,4,0,2,8,7,3,5]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p52 : Aut := by
  let f : V → V := ![4,3,2,1,0,9,8,7,6,5]
  let g : V → V := ![4,3,2,1,0,9,8,7,6,5]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p53 : Aut := by
  let f : V → V := ![4,3,2,7,9,0,8,1,5,6]
  let g : V → V := ![5,7,2,1,0,8,9,3,6,4]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p54 : Aut := by
  let f : V → V := ![4,3,8,5,0,9,2,6,7,1]
  let g : V → V := ![4,9,6,1,0,3,7,8,2,5]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p55 : Aut := by
  let f : V → V := ![4,3,8,6,9,0,2,5,1,7]
  let g : V → V := ![5,8,6,1,0,7,3,9,2,4]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p56 : Aut := by
  let f : V → V := ![4,9,6,1,0,3,7,8,2,5]
  let g : V → V := ![4,3,8,5,0,9,2,6,7,1]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p57 : Aut := by
  let f : V → V := ![4,9,6,8,3,0,7,1,5,2]
  let g : V → V := ![5,7,9,4,0,8,2,6,3,1]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p58 : Aut := by
  let f : V → V := ![4,9,7,2,3,0,6,5,1,8]
  let g : V → V := ![5,8,3,4,0,7,6,2,9,1]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p59 : Aut := by
  let f : V → V := ![4,9,7,5,0,3,6,2,8,1]
  let g : V → V := ![4,9,7,5,0,3,6,2,8,1]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p60 : Aut := by
  let f : V → V := ![5,0,1,2,7,8,4,6,3,9]
  let g : V → V := ![1,2,3,8,6,0,7,4,5,9]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p61 : Aut := by
  let f : V → V := ![5,0,1,6,8,7,4,2,9,3]
  let g : V → V := ![1,2,7,9,6,0,3,5,4,8]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p62 : Aut := by
  let f : V → V := ![5,0,4,3,8,7,1,9,2,6]
  let g : V → V := ![1,6,8,3,2,0,9,5,4,7]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p63 : Aut := by
  let f : V → V := ![5,0,4,9,7,8,1,3,6,2]
  let g : V → V := ![1,6,9,7,2,0,8,4,5,3]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p64 : Aut := by
  let f : V → V := ![5,7,2,1,0,8,9,3,6,4]
  let g : V → V := ![4,3,2,7,9,0,8,1,5,6]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p65 : Aut := by
  let f : V → V := ![5,7,2,3,8,0,9,1,4,6]
  let g : V → V := ![5,7,2,3,8,0,9,1,4,6]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p66 : Aut := by
  let f : V → V := ![5,7,9,4,0,8,2,6,3,1]
  let g : V → V := ![4,9,6,8,3,0,7,1,5,2]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p67 : Aut := by
  let f : V → V := ![5,7,9,6,8,0,2,4,1,3]
  let g : V → V := ![5,8,6,9,7,0,3,1,4,2]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p68 : Aut := by
  let f : V → V := ![5,8,3,2,7,0,6,4,1,9]
  let g : V → V := ![5,8,3,2,7,0,6,4,1,9]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p69 : Aut := by
  let f : V → V := ![5,8,3,4,0,7,6,2,9,1]
  let g : V → V := ![4,9,7,2,3,0,6,5,1,8]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p70 : Aut := by
  let f : V → V := ![5,8,6,1,0,7,3,9,2,4]
  let g : V → V := ![4,3,8,6,9,0,2,5,1,7]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p71 : Aut := by
  let f : V → V := ![5,8,6,9,7,0,3,1,4,2]
  let g : V → V := ![5,7,9,6,8,0,2,4,1,3]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p72 : Aut := by
  let f : V → V := ![6,1,0,4,9,8,2,5,3,7]
  let g : V → V := ![2,1,6,8,3,7,0,9,5,4]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p73 : Aut := by
  let f : V → V := ![6,1,0,5,8,9,2,4,7,3]
  let g : V → V := ![2,1,6,9,7,3,0,8,4,5]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p74 : Aut := by
  let f : V → V := ![6,1,2,3,8,9,0,7,4,5]
  let g : V → V := ![6,1,2,3,8,9,0,7,4,5]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p75 : Aut := by
  let f : V → V := ![6,1,2,7,9,8,0,3,5,4]
  let g : V → V := ![6,1,2,7,9,8,0,3,5,4]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p76 : Aut := by
  let f : V → V := ![6,8,3,2,1,9,5,4,7,0]
  let g : V → V := ![9,4,3,2,7,6,0,8,1,5]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p77 : Aut := by
  let f : V → V := ![6,8,3,4,9,1,5,2,0,7]
  let g : V → V := ![8,5,7,2,3,6,0,9,1,4]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p78 : Aut := by
  let f : V → V := ![6,8,5,0,1,9,3,7,4,2]
  let g : V → V := ![3,4,9,6,8,2,0,7,1,5]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p79 : Aut := by
  let f : V → V := ![6,8,5,7,9,1,3,0,2,4]
  let g : V → V := ![7,5,8,6,9,2,0,3,1,4]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p80 : Aut := by
  let f : V → V := ![6,9,4,0,1,8,7,3,5,2]
  let g : V → V := ![3,4,9,7,2,8,0,6,5,1]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p81 : Aut := by
  let f : V → V := ![6,9,4,3,8,1,7,0,2,5]
  let g : V → V := ![7,5,8,3,2,9,0,6,4,1]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p82 : Aut := by
  let f : V → V := ![6,9,7,2,1,8,4,5,3,0]
  let g : V → V := ![9,4,3,8,6,7,0,2,5,1]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p83 : Aut := by
  let f : V → V := ![6,9,7,5,8,1,4,2,0,3]
  let g : V → V := ![8,5,7,9,6,3,0,2,4,1]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p84 : Aut := by
  let f : V → V := ![7,2,1,0,5,9,3,6,4,8]
  let g : V → V := ![3,2,1,6,8,4,7,0,9,5]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p85 : Aut := by
  let f : V → V := ![7,2,1,6,9,5,3,0,8,4]
  let g : V → V := ![7,2,1,6,9,5,3,0,8,4]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p86 : Aut := by
  let f : V → V := ![7,2,3,4,9,5,1,8,0,6]
  let g : V → V := ![8,6,1,2,3,5,9,0,7,4]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p87 : Aut := by
  let f : V → V := ![7,2,3,8,5,9,1,4,6,0]
  let g : V → V := ![9,6,1,2,7,4,8,0,3,5]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p88 : Aut := by
  let f : V → V := ![7,5,0,1,2,9,8,4,6,3]
  let g : V → V := ![2,3,4,9,7,1,8,0,6,5]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p89 : Aut := by
  let f : V → V := ![7,5,0,4,9,2,8,1,3,6]
  let g : V → V := ![2,7,5,8,3,1,9,0,6,4]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p90 : Aut := by
  let f : V → V := ![7,5,8,3,2,9,0,6,4,1]
  let g : V → V := ![6,9,4,3,8,1,7,0,2,5]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p91 : Aut := by
  let f : V → V := ![7,5,8,6,9,2,0,3,1,4]
  let g : V → V := ![6,8,5,7,9,1,3,0,2,4]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p92 : Aut := by
  let f : V → V := ![7,9,4,0,5,2,6,3,1,8]
  let g : V → V := ![3,8,5,7,2,4,6,0,9,1]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p93 : Aut := by
  let f : V → V := ![7,9,4,3,2,5,6,0,8,1]
  let g : V → V := ![7,9,4,3,2,5,6,0,8,1]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p94 : Aut := by
  let f : V → V := ![7,9,6,1,2,5,4,8,0,3]
  let g : V → V := ![8,3,4,9,6,5,2,0,7,1]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p95 : Aut := by
  let f : V → V := ![7,9,6,8,5,2,4,1,3,0]
  let g : V → V := ![9,7,5,8,6,4,2,0,3,1]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p96 : Aut := by
  let f : V → V := ![8,3,2,1,6,5,4,7,0,9]
  let g : V → V := ![8,3,2,1,6,5,4,7,0,9]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p97 : Aut := by
  let f : V → V := ![8,3,2,7,5,6,4,1,9,0]
  let g : V → V := ![9,7,2,1,6,4,5,3,0,8]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p98 : Aut := by
  let f : V → V := ![8,3,4,0,5,6,2,9,1,7]
  let g : V → V := ![3,8,6,1,2,4,5,9,0,7]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p99 : Aut := by
  let f : V → V := ![8,3,4,9,6,5,2,0,7,1]
  let g : V → V := ![7,9,6,1,2,5,4,8,0,3]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p100 : Aut := by
  let f : V → V := ![8,5,0,1,6,3,7,4,2,9]
  let g : V → V := ![2,3,8,5,7,1,4,6,0,9]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p101 : Aut := by
  let f : V → V := ![8,5,0,4,3,6,7,1,9,2]
  let g : V → V := ![2,7,9,4,3,1,5,6,0,8]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p102 : Aut := by
  let f : V → V := ![8,5,7,2,3,6,0,9,1,4]
  let g : V → V := ![6,8,3,4,9,1,5,2,0,7]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p103 : Aut := by
  let f : V → V := ![8,5,7,9,6,3,0,2,4,1]
  let g : V → V := ![6,9,7,5,8,1,4,2,0,3]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p104 : Aut := by
  let f : V → V := ![8,6,1,0,5,3,9,2,4,7]
  let g : V → V := ![3,2,7,5,8,4,1,9,0,6]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p105 : Aut := by
  let f : V → V := ![8,6,1,2,3,5,9,0,7,4]
  let g : V → V := ![7,2,3,4,9,5,1,8,0,6]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p106 : Aut := by
  let f : V → V := ![8,6,9,4,3,5,1,7,0,2]
  let g : V → V := ![8,6,9,4,3,5,1,7,0,2]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p107 : Aut := by
  let f : V → V := ![8,6,9,7,5,3,1,4,2,0]
  let g : V → V := ![9,6,8,5,7,4,1,3,0,2]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p108 : Aut := by
  let f : V → V := ![9,4,0,1,6,7,3,5,2,8]
  let g : V → V := ![2,3,8,6,1,7,4,5,9,0]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p109 : Aut := by
  let f : V → V := ![9,4,0,5,7,6,3,1,8,2]
  let g : V → V := ![2,7,9,6,1,3,5,4,8,0]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p110 : Aut := by
  let f : V → V := ![9,4,3,2,7,6,0,8,1,5]
  let g : V → V := ![6,8,3,2,1,9,5,4,7,0]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p111 : Aut := by
  let f : V → V := ![9,4,3,8,6,7,0,2,5,1]
  let g : V → V := ![6,9,7,2,1,8,4,5,3,0]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p112 : Aut := by
  let f : V → V := ![9,6,1,0,4,7,8,2,5,3]
  let g : V → V := ![3,2,7,9,4,8,1,5,6,0]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p113 : Aut := by
  let f : V → V := ![9,6,1,2,7,4,8,0,3,5]
  let g : V → V := ![7,2,3,8,5,9,1,4,6,0]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p114 : Aut := by
  let f : V → V := ![9,6,8,3,4,7,1,5,2,0]
  let g : V → V := ![9,6,8,3,4,7,1,5,2,0]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p115 : Aut := by
  let f : V → V := ![9,6,8,5,7,4,1,3,0,2]
  let g : V → V := ![8,6,9,7,5,3,1,4,2,0]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p116 : Aut := by
  let f : V → V := ![9,7,2,1,6,4,5,3,0,8]
  let g : V → V := ![8,3,2,7,5,6,4,1,9,0]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p117 : Aut := by
  let f : V → V := ![9,7,2,3,4,6,5,1,8,0]
  let g : V → V := ![9,7,2,3,4,6,5,1,8,0]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p118 : Aut := by
  let f : V → V := ![9,7,5,0,4,6,2,8,1,3]
  let g : V → V := ![3,8,6,9,4,2,5,1,7,0]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
private def p119 : Aut := by
  let f : V → V := ![9,7,5,8,6,4,2,0,3,1]
  let g : V → V := ![7,9,6,8,5,2,4,1,3,0]
  exact ⟨⟨f,g,by decide,by decide⟩,by decide⟩
def group : Array Aut := #[p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,p40,p41,p42,p43,p44,p45,p46,p47,p48,p49,p50,p51,p52,p53,p54,p55,p56,p57,p58,p59,p60,p61,p62,p63,p64,p65,p66,p67,p68,p69,p70,p71,p72,p73,p74,p75,p76,p77,p78,p79,p80,p81,p82,p83,p84,p85,p86,p87,p88,p89,p90,p91,p92,p93,p94,p95,p96,p97,p98,p99,p100,p101,p102,p103,p104,p105,p106,p107,p108,p109,p110,p111,p112,p113,p114,p115,p116,p117,p118,p119]
def signedID : V → V → Nat := ![![0,0,0,4,4,5,2,5,7,6],![12,0,48,48,12,13,50,49,50,51],![24,24,0,40,40,41,72,41,100,101],![28,36,36,0,28,44,98,104,44,78],![16,16,52,52,0,21,54,59,56,54],![17,17,53,58,20,0,55,53,55,57],![26,26,74,102,43,42,0,103,42,43],![29,37,37,105,45,29,99,0,79,45],![30,38,96,46,46,30,38,77,0,106],![31,39,97,76,31,47,39,47,107,0]]
def physicalID : V → V → Nat := ![![0,0,0,4,4,5,2,5,7,6],![0,0,0,0,0,1,2,1,2,3],![0,0,0,0,4,5,0,1,0,1],![4,0,0,0,4,10,2,4,8,4],![4,0,4,4,0,8,6,11,8,6],![5,1,5,10,8,0,7,5,7,9],![2,2,0,2,6,7,0,3,2,3],![5,1,1,4,11,5,3,0,5,9],![7,2,0,8,8,7,2,5,0,6],![6,3,1,4,6,9,3,9,6,0]]
def physicalA : V → V → V := ![![0,0,0,0,0,0,0,0,0,0],![0,1,1,1,1,1,1,1,1,1],![0,1,2,2,1,1,2,2,2,2],![0,1,2,3,1,1,2,2,2,2],![0,1,1,1,4,1,1,1,1,1],![0,1,1,1,1,5,1,1,1,1],![0,1,2,2,1,1,6,2,2,2],![0,1,2,2,1,1,2,7,2,2],![0,1,2,2,1,1,2,2,8,2],![0,1,2,2,1,1,2,2,2,9]]
def physicalB : V → V → V := ![![0,1,2,2,1,1,2,2,2,2],![1,1,2,3,4,4,2,3,3,3],![2,2,2,3,3,3,6,3,8,8],![2,3,3,3,2,3,8,8,3,6],![1,4,3,2,4,4,3,3,3,2],![1,4,3,3,4,5,3,2,2,3],![2,2,6,8,3,3,6,8,3,3],![2,3,3,8,3,2,8,7,6,3],![2,3,8,3,3,2,3,6,8,8],![2,3,8,6,2,3,3,3,8,9]]
def signed (i j : V) : Aut := group.getD (signedID i j) p0
def physical (i j : V) : Aut := group.getD (physicalID i j) p0

set_option maxRecDepth 16000
set_option maxHeartbeats 0
theorem signed_pair (i j : V) (ne : i ≠ j) :
    (signed i j).toEquiv i = 0 ∧
      (signed i j).toEquiv j = (if code i j then 1 else 2) := by
  revert i j; decide +kernel

theorem physical_pair (i j : V) (ne : i ≠ j) :
    (physical i j).toEquiv 0 = 0 ∧
    (((physical i j).toEquiv i = physicalA i j ∧ (physical i j).toEquiv j = physicalB i j) ∨
     ((physical i j).toEquiv j = physicalA i j ∧ (physical i j).toEquiv i = physicalB i j)) := by
  revert i j; decide +kernel

def physicalRepresentatives : List (V × V) := [(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,6),(2,8)]
theorem physical_cover (i j : V) (ne : i ≠ j) :
    (physicalA i j,physicalB i j) ∈ physicalRepresentatives := by
  revert i j; decide +kernel

#print axioms signed_pair
#print axioms physical_pair
#print axioms physical_cover
end PetersenVerifiedGroup
