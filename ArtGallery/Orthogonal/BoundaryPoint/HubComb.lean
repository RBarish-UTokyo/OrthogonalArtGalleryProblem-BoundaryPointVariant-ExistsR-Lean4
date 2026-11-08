module

public import ArtGallery.Orthogonal.BoundaryPoint.HubFeatures
public import ArtGallery.Orthogonal.BoundaryPoint.PlacedSlots
public import Mathlib.Data.List.Pairwise

/-! # Simplicity of the hub with its western step closed to the low roof -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubComb
open HubFeatures BoundaryChart ArtGallery.Stade.Chain ArtGallery.Orthogonal.Hard BankCoordinates RectContour

def floorTags (rows : Nat) (ss : List ℚ) := (List.range rows).reverse.map footTag ++ ss.tail.map dividerTag
def ceilTags (rows : Nat) (ss : List ℚ) := ss.reverse.map shaftTag ++ (List.range rows).map capTag
def L (k : Nat) := door k-30-1/10
def R (ss : List ℚ) := ss.getLastD 0+10
def virtual (n k : Nat) (ss : List ℚ) : Polygon :=
  let f := 1-D n
  ⟨[(L k,f)].map ratPoint++((floorTags (k+1) ss).map (trace f)).flatten++
    [(R ss,f),(R ss,-6)].map ratPoint++((ceilTags (k+1) ss).map (trace f)).flatten++
    [(L k,-6)].map ratPoint⟩

structure Placed (ss : List ℚ) : Prop where
  exists_slot : ss≠[]
  far : ∀ x∈ss,1970<x
  sorted : ss.Pairwise fun x y => x+10≤y

theorem last_bound {ss : List ℚ} (order : Placed ss) (x : ℚ) (hx : x∈ss) : x≤ss.getLastD 0 := by
  have weak : ss.Pairwise (·≤·) := order.sorted.imp fun h => by linarith
  simpa [List.getLastD_eq_getLast?,List.getLast?_eq_some_getLast order.exists_slot] using weak.rel_getLast hx

private theorem range_gap {i j : Nat} (lt : i<j) : door j+2000≤door i := by
  have gap : (i:ℚ)+1≤j := by exact_mod_cast lt
  unfold door; linarith
private theorem range_le {i j : Nat} (le : i≤j) : door j≤door i := by
  unfold door; exact mul_le_mul_of_nonpos_left (by exact_mod_cast le) (by norm_num)
private theorem not_positive (j : Nat) : door j≤0 := by unfold door; exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)

private theorem enough_space {ss : List ℚ} (placed : Placed ss) : 1970<ss.getLastD 0 := by
  have last := ss.getLast_mem placed.exists_slot
  exact (placed.far _ last).trans_le (last_bound placed _ last)

theorem floor_positions {ss : List ℚ} (placed : Placed ss) (k : Nat) :
    (∀ F∈floorTags (k+1) ss, onFloor F=true ∧ L k<west F ∧ east F<R ss) ∧
    (floorTags (k+1) ss).Pairwise (fun F G => east F<west G) := by
  have high := enough_space placed
  constructor
  · intro F h
    rcases List.mem_append.mp h with ft|dv
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ft
      have lower := range_le (Nat.le_of_lt_succ (List.mem_range.mp (List.mem_reverse.mp hj)))
      have upper := not_positive j
      exact ⟨rfl,by dsimp [L,west,footTag]; linarith,by dsimp [R,east,footTag]; linarith⟩
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp dv
      have h := List.mem_of_mem_tail hx
      have w := placed.far x h
      have u := last_bound placed x h
      exact ⟨rfl,by dsimp [L,west,dividerTag]; linarith [not_positive k],by dsimp [R,east,dividerTag]; linarith⟩
  apply List.pairwise_append.mpr
  refine ⟨?_,?_,?_⟩
  · apply List.pairwise_map.mpr
    apply List.pairwise_reverse.mpr
    apply List.pairwise_lt_range.imp
    intro i j h; dsimp [east,west,footTag]; linarith [range_gap h]
  · apply List.pairwise_map.mpr; apply placed.sorted.tail.imp
    intro x y gap; dsimp [east,west,dividerTag]; linarith
  · intro F hF G hG
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hF
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hG
    dsimp [east,west,footTag,dividerTag]
    linarith [not_positive j,placed.far x (List.mem_of_mem_tail hx)]

theorem ceiling_positions {ss : List ℚ} (placed : Placed ss) (k : Nat) :
    (∀ F∈ceilTags (k+1) ss, onFloor F=false ∧ L k<west F ∧ east F<R ss) ∧
    (ceilTags (k+1) ss).Pairwise (fun F G => east G<west F) := by
  have high := enough_space placed
  constructor
  · intro F h
    rcases List.mem_append.mp h with shaft|cap
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp shaft
      have h := List.mem_reverse.mp hx
      have w := placed.far x h
      have u := last_bound placed x h
      exact ⟨rfl,by dsimp [L,west,shaftTag]; linarith [not_positive k],by dsimp [R,east,shaftTag]; linarith⟩
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp cap
      have lower := range_le (Nat.le_of_lt_succ (List.mem_range.mp hj))
      exact ⟨rfl,by dsimp [L,west,capTag]; linarith,by dsimp [R,east,capTag]; linarith [not_positive j]⟩
  apply List.pairwise_append.mpr
  refine ⟨?_,?_,?_⟩
  · apply List.pairwise_map.mpr
    apply List.pairwise_reverse.mpr
    apply placed.sorted.imp
    intro x y gap; dsimp [east,west,shaftTag]; linarith
  · apply List.pairwise_map.mpr
    apply List.pairwise_lt_range.imp
    intro i j h; dsimp [east,west,capTag]; linarith [range_gap h]
  · intro F hF G hG
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hF
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hG
    dsimp [east,west,capTag,shaftTag]
    linarith [not_positive j,placed.far x (List.mem_reverse.mp hx)]

theorem simple_virtual {ss : List ℚ} (placed : Placed ss) (n k : Nat) (big : 65≤n) : (virtual n k ss).Simple := by
  let f := 1-D n
  have bn : (65:ℚ)≤n := by exact_mod_cast big
  have low : f< -7 := by dsimp [f,D,BankCoordinates.k]; nlinarith [mul_self_le_mul_self (by norm_num : (0:ℚ)≤65) bn]
  have lowR : (f:ℝ)< -7 := by exact_mod_cast low
  obtain ⟨FL,FO⟩ := floor_positions placed k
  obtain ⟨CL,CO⟩ := ceiling_positions placed k
  have lr : (L k:ℝ)<R ss := by
    apply Rat.cast_lt.mpr; dsimp [L,R]; linarith [not_positive k,enough_space placed]
  have full := simple_of_combsD (ylo:=(f:ℝ)) (yhi:=(-6:ℝ)) (m:=-13/2) lr (by linarith) (by norm_num)
    ((floorTags (k+1) ss).map (trace f)) ((ceilTags (k+1) ss).map (trace f))
    (by intro g hg; obtain ⟨F,hF,rfl⟩ := List.mem_map.mp hg; exact floor low F (FL F hF).1 (FL F hF).2.1 (FL F hF).2.2)
    (by intro g hg; obtain ⟨F,hF,rfl⟩ := List.mem_map.mp hg; apply chainSet_snd_lt; intro p hp; simpa only [(FL F hF).1,ite_true] using half f low F hp)
    (List.pairwise_map.mpr (FO.imp (fun h => ⟨(gap f h).1,(gap f h).2.1⟩)))
    (by intro g hg; obtain ⟨F,hF,rfl⟩ := List.mem_map.mp hg; exact ceiling low F (CL F hF).1 (CL F hF).2.1 (CL F hF).2.2)
    (by intro g hg; obtain ⟨F,hF,rfl⟩ := List.mem_map.mp hg; apply chainSet_snd_gt; intro p hp; simpa only [(CL F hF).1,Bool.false_eq_true,ite_false] using half f low F hp)
    (List.pairwise_map.mpr (CO.imp (fun h => ⟨(gap f h).1.symm,(gap f h).2.2⟩)))
  simpa only [virtual,List.map_cons,List.map_nil,ratPoint,Rat.cast_neg,Rat.cast_ofNat,f] using full

end ArtGallery.Orthogonal.BoundaryPoint.HubComb
end
