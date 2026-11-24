import PetersenWordCost
import PetersenFrontier

open PetersenSignedBridge PetersenWordCost PetersenFrontier
namespace PetersenPackedFrontier

section Map
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem map_trace {G : α → α → α → Prop} {H : β → β → β → Prop} (e : α ↪ β)
    (step : ∀ a b o, G a b o → H (e a) (e b) (e o)) {I W m c}
    (r : Trace G I m c W) : Trace H (I.map e) m c (W.map e) := by
  induction r with
  | start => exact Trace.start
  | @step m c K a b o _ ne fresh g ih =>
    simp only [Finset.map_insert] at ih ⊢
    have fresh' : e o ∉ insert (e a) (insert (e b) (K.map e)) := by
      simpa only [← Finset.map_insert,Finset.mem_map',Function.Embedding.coeFn_mk] using fresh
    have cr : credit (e a) (e b) (K.map e) = credit a b K := by simp [credit]
    rw [← cr]
    exact Trace.step ih (fun q => ne (e.injective q)) fresh' (step _ _ _ g)

end Map

theorem pack_read {w : Nat} (a : BitVec w) : pack (read a) = a := read_inj (read_pack _)

def embed (w : Nat) : Func (Fin w) ↪ BitVec w :=
  ⟨pack, fun _ _ h => by simpa only [read_pack] using congrArg read h⟩

def norm {w : Nat} (a : BitVec w) : BitVec w := if a.getLsbD 0 then ~~~a else a

theorem pack_flip {w : Nat} (f : Func (Fin w)) : pack (flip f) = ~~~pack f := by
  apply read_inj
  rw [read_pack]
  funext i
  have eq := congrFun (read_pack f) i
  simpa [PetersenWordCost.read,PetersenFrontier.flip,i.isLt] using congrArg Bool.not eq.symm

theorem pack_norm {w : Nat} (hw : 0 < w) (f : Func (Fin w)) :
    pack (signedKey ⟨0,hw⟩ f) = norm (pack f) := by
  have e := congrFun (read_pack f) ⟨0,hw⟩
  change (pack f).getLsbD 0 = f ⟨0,hw⟩ at e
  cases h : f ⟨0,hw⟩ <;> simp [signedKey,norm,e,h,pack_flip]

theorem pack_bin {w} (op : Bool) (f g : Func (Fin w)) :
    pack (bin op f g) = gate op (pack f) (pack g) := by
  apply read_inj
  rw [read_pack]
  funext i
  have a := congrFun (read_pack f) i
  have b := congrFun (read_pack g) i
  change (pack f).getLsbD i.val = f i at a
  change (pack g).getLsbD i.val = g i at b
  cases op <;> simp [bin,gate,PetersenWordCost.read] at * <;> simp [a,b]

def options {w} (a b : BitVec w) : List (BitVec w) :=
  ([a,~~~a].product [b,~~~b]).flatMap fun (p,q) =>
    [norm (p &&& q),norm (p ||| q)]

def signedWordGate {w} (a b o : BitVec w) : Prop := o ∈ options a b

theorem rep {w} (p : BitVec w) : p ∈ [norm p,~~~(norm p)] := by
  by_cases h : p.getLsbD 0 = true <;> simp [norm,h]

theorem mapped_gate {w : Nat} (hw : 0 < w) {a b o : Func (Fin w)}
    (g : keyedGate (signedKey ⟨0,hw⟩) a b o) :
    signedWordGate (pack a) (pack b) (pack o) := by
  obtain ⟨p,q,j,rfl,rfl,rfl,_⟩ := g
  simp only [signedWordGate,options,pack_norm,pack_bin]
  apply List.mem_flatMap.mpr
  refine ⟨(pack p,pack q),List.mem_product.mpr ⟨rep _,rep _⟩,?_⟩
  cases j <;> simp [gate]

set_option backward.isDefEq.respectTransparency false in
/-- Exact source coverage on finite truth words, after deleting unused inputs and
normalizing at assignment 0. No memoization or completeness hypothesis is used. -/
theorem realize {w : Nat} (hw : 0 < w) (I : List (BitVec w)) (target : BitVec w)
    (normI : ∀ a ∈ I, a.getLsbD 0 = false) (normT : target.getLsbD 0 = false)
    (hotT : nonconstant (read target)) {k W} (r : Run (I.map read) k W) (out : Av W (read target)) :
    ∃ U ⊆ I.toFinset, ∃ m ≤ k, ∃ c, Trace signedWordGate U m c {target} ∧ m+1=U.card+c := by
  classical
  letI : DecidableEq (Func (Fin w)) := Classical.decEq _
  let F := (I.map read).toFinset
  have normal (a : BitVec w) (h : a.getLsbD 0 = false) :
      signedKey ⟨0,hw⟩ (read a) = read a := by simp [signedKey,PetersenWordCost.read,h]
  have hi : ∀ f ∈ I.map read, nonconstant f → signedKey ⟨0,hw⟩ f ∈ F := by
    intro f h _
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    rw [normal a (normI a ha)]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩)
  obtain ⟨j,hj,S,p,cov⟩ := signed_prefix ⟨0,hw⟩ r F hi
  have ht := av_coverage ⟨0,hw⟩ cov out hotT
  rw [normal _ normT] at ht
  obtain ⟨U,sub,m,hm,c,tr⟩ := p.schedule {read target} (Finset.singleton_subset_iff.mpr ht)
  have mapped := map_trace (embed w) (fun _ _ _ g => mapped_gate hw g) tr
  have e : (embed w) (read target) = target := pack_read _
  simp only [Finset.map_singleton,e] at mapped
  have hU : U.map (embed w) ⊆ I.toFinset := by
    intro a ha
    obtain ⟨f,hf,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (sub hf))
    change pack (read b) ∈ I.toFinset
    rw [pack_read]
    exact List.mem_toFinset.mpr hb
  exact ⟨_,hU,m,by omega,c,mapped,mapped.sink⟩

#print axioms realize

end PetersenPackedFrontier
