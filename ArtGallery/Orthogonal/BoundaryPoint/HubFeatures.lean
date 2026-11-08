module

public import ArtGallery.Orthogonal.BoundaryPoint.HubSky
public import ArtGallery.Orthogonal.Hard.Comb

/-! # The four kinds of boundary features of the common hub
The virtual last ceiling cap is closed down to the low roof. The physical
western boundary is recovered by replacing the two final vertices. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubFeatures
open ArtGallery.Stade.Chain ArtGallery.Orthogonal.Hard BoundaryChart RectContour BankCoordinates
open Set

inductive Kind where | foot | divider | shaft | cap
structure Feature where
  kind : Kind
  anchor : ℚ

def onFloor (F : Feature) : Bool := match F.kind with | .foot | .divider => true | _ => false
def west (F : Feature) : ℚ := match F.kind with
  | .foot => F.anchor+99 | .divider => F.anchor-3 | .shaft => F.anchor | .cap => F.anchor-30
def east (F : Feature) : ℚ := match F.kind with
  | .foot => F.anchor+101 | .divider => F.anchor-2 | .shaft => F.anchor+3/2 | .cap => F.anchor+110+1/10

def xLines (F : Feature) : List ℚ := match F.kind with
  | .foot => [F.anchor+100-1/1000,F.anchor+100+1/1000]
  | .divider => [F.anchor-2-1,F.anchor-2-1/10,F.anchor-2]
  | .shaft => [F.anchor,F.anchor+3/2]
  | .cap => [F.anchor-30,F.anchor+110,F.anchor+110+1/10]
def yLines (f : ℚ) : Kind → List ℚ
  | .foot => [2*f,f]
  | .divider => [f,f+1/100000000,f+1/4]
  | .shaft => [-6,-6-f]
  | .cap => [-6,1-1/10000,1]
def pattern : Kind → List (Nat × Nat)
  | .foot => [(0,1),(0,0),(1,0),(1,1)]
  | .divider => [(0,0),(0,2),(2,2),(2,1),(1,1),(1,0)]
  | .shaft => [(1,0),(1,1),(0,1),(0,0)]
  | .cap => [(1,0),(1,1),(2,1),(2,2),(0,2),(0,0)]

def trace (f : ℚ) (F : Feature) : List Point :=
  (pattern F.kind).map (gridPt ((xLines F).map ((↑) : ℚ → ℝ)) ((yLines f F.kind).map ((↑) : ℚ → ℝ)))

def footTag (j : Nat) : Feature := ⟨.foot,door j⟩
def dividerTag (x : ℚ) : Feature := ⟨.divider,x⟩
def shaftTag (x : ℚ) : Feature := ⟨.shaft,x⟩
def capTag (j : Nat) : Feature := ⟨.cap,door j⟩

theorem foot_trace (f : ℚ) (j : Nat) : trace f (footTag j)=(BoundaryChart.foot f j).map ratPoint := by
  rfl
theorem divider_trace (f x : ℚ) : trace f (dividerTag x)=(BoundaryChart.divider f x).map ratPoint := by
  rfl
theorem shaft_trace (f x : ℚ) : trace f (shaftTag x)=(BoundaryChart.shaft f x).map ratPoint := by
  rfl
theorem cap_trace (f : ℚ) (j : Nat) : trace f (capTag j)=(capPath (j+2) j).map ratPoint := by
  simp only [capPath,show j+1<j+2 by omega,ite_true]; rfl

private theorem x_order (F : Feature) : ((xLines F).map ((↑) : ℚ → ℝ)).IsChain (·<·) := by
  rcases F with ⟨k,a⟩; cases k <;> simp [xLines,List.isChain_cons_cons] <;> try norm_num <;> try linarith

private theorem y_order {f : ℚ} (hf : f< -7) (k : Kind) : ((yLines f k).map ((↑) : ℚ → ℝ)).IsChain (·<·) := by
  have low : (f:ℝ)< -7 := by exact_mod_cast hf
  cases k <;> simp [yLines,List.isChain_cons_cons] <;> try norm_num <;> try linarith

private theorem indices (f : ℚ) (F : Feature) (p : Nat × Nat) (h : p∈pattern F.kind) :
    p.1<((xLines F).map ((↑) : ℚ → ℝ)).length ∧ p.2<((yLines f F.kind).map ((↑) : ℚ → ℝ)).length := by
  rcases F with ⟨k,a⟩; cases k <;> simp [pattern] at h <;> rcases h with h|h|h|h <;>
    first | subst p | rcases h with rfl|rfl|rfl
  all_goals norm_num [xLines,yLines]

theorem span (f : ℚ) (F : Feature) {p : Point} (h : p∈trace f F) : (west F:ℝ)≤p.1 ∧ p.1≤(east F:ℝ) := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
  rcases F with ⟨k,a⟩; cases k <;> simp [pattern] at hi
  all_goals
    rcases hi with h|h|h|h <;> first | subst i | rcases h with rfl|rfl|rfl
    all_goals norm_num [gridPt,xLines,west,east]
  all_goals first | constructor <;> linarith | linarith

theorem half (f : ℚ) (hf : f< -7) (F : Feature) {p : Point} (hp : p∈trace f F) :
    if onFloor F then p.2< -13/2 else -13/2<p.2 := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  have low : (f:ℝ)< -7 := by exact_mod_cast hf
  rcases F with ⟨k,a⟩; cases k <;> simp [pattern] at hi
  all_goals
    rcases hi with h|h|h|h <;> first | subst i | rcases h with rfl|rfl|rfl
    all_goals norm_num [gridPt,yLines,onFloor] <;> linarith

theorem trace_span (f : ℚ) (F : Feature) {q : Point} (h : q∈chainSet (trace f F)) :
    (west F:ℝ)≤q.1 ∧ q.1≤(east F:ℝ) := by
  have interval : Convex ℝ {x : Point | (west F:ℝ)≤x.1 ∧ x.1≤(east F:ℝ)} := by
    intro p hp u hu a b ha hb total
    change _ ∧ _ at hp hu
    change _≤a*p.1+b*u.1 ∧ a*p.1+b*u.1≤_
    exact ⟨by nlinarith only [total,mul_nonneg ha (sub_nonneg.mpr hp.1),mul_nonneg hb (sub_nonneg.mpr hu.1),
           show (a+b)*(west F:ℝ)=(west F:ℝ) by rw [total,one_mul]],
      by nlinarith only [mul_nonneg ha (sub_nonneg.mpr hp.2),mul_nonneg hb (sub_nonneg.mpr hu.2),
           show (a+b)*(east F:ℝ)=(east F:ℝ) by rw [total,one_mul]]⟩
  exact chainSet_subset_of_convex interval (fun _ hp => span f F hp) h

private theorem first_mem (f : ℚ) (F : Feature) : 2≤(trace f F).length := by
  rcases F with ⟨k,a⟩; cases k <;> norm_num [trace,pattern]

theorem gap {F G : Feature} (f : ℚ) (h : east F<west G) :
    Disjoint (chainSet (trace f F)) (chainSet (trace f G)) ∧
      (lstPt (trace f F)).1<(fstPt (trace f G)).1 ∧ (fstPt (trace f F)).1<(lstPt (trace f G)).1 := by
  have gap : (east F:ℝ)<west G := by exact_mod_cast h
  constructor
  · exact Set.disjoint_left.mpr (fun p hF hG => (not_le_of_gt gap) ((trace_span f _ hG).1.trans (trace_span f _ hF).2))
  · constructor
    · exact (span f F (lstPt_mem_list (first_mem f F))).2.trans_lt (gap.trans_le (span f G (fstPt_mem_list (first_mem f G))).1)
    · exact (span f F (fstPt_mem_list (first_mem f F))).2.trans_lt (gap.trans_le (span f G (lstPt_mem_list (first_mem f G))).1)

private theorem x_bound (F : Feature) {l r f : ℚ} (lo : l<west F) (hi : east F<r) {q : Nat × Nat} (hq : q∈pattern F.kind) :
    (l:ℝ)<((xLines F).map ((↑) : ℚ → ℝ)).getD q.1 0 ∧ ((xLines F).map ((↑) : ℚ → ℝ)).getD q.1 0<(r:ℝ) := by
  have h := span f F (List.mem_map_of_mem hq)
  exact ⟨(Rat.cast_lt.mpr lo).trans_le h.1,h.2.trans_lt (Rat.cast_lt.mpr hi)⟩

theorem floor {f l r : ℚ} (hf : f< -7) (F : Feature) (floor : onFloor F=true) (lo : l<west F) (hi : east F<r) :
    FloorFeatureD f l r (trace f F) := by
  let j := if F.kind matches .foot then 1 else 0
  have lev : (((yLines f F.kind).map ((↑) : ℚ → ℝ)).getD j 0)=(f:ℝ) := by
    rcases F with ⟨k,v⟩; cases k <;> first | rfl | contradiction
  rw [←lev]
  apply floorFeatureD_of_grid (x_order F) (y_order hf _) (indices f F) _ _ (fun p hp => x_bound (f:=f) F lo hi hp)
  · rcases F with ⟨k,v⟩; cases k <;> norm_num [j,yLines]
  · rcases F with ⟨k,v⟩; cases k <;> simp [onFloor] at floor
    all_goals dsimp [j,pattern]; decide +kernel

theorem ceiling {f l r : ℚ} (hf : f< -7) (F : Feature) (ceil : onFloor F=false) (lo : l<west F) (hi : east F<r) :
    CeilFeatureD (-6) l r (trace f F) := by
  have lev : (((yLines f F.kind).map ((↑) : ℚ → ℝ)).getD 0 0)=(-6:ℝ) := by
    rcases F with ⟨k,v⟩; cases k <;> simp [onFloor] at ceil
    all_goals norm_num [yLines]
  rw [←lev]
  apply ceilFeatureD_of_grid (x_order F) (y_order hf _) (indices f F) _ _ (fun p hp => x_bound (f:=f) F lo hi hp)
  · rcases F with ⟨k,v⟩; cases k <;> norm_num [yLines]
  · rcases F with ⟨k,v⟩; cases k <;> simp [onFloor] at ceil
    all_goals dsimp only [pattern]; decide +kernel

end ArtGallery.Orthogonal.BoundaryPoint.HubFeatures
end
