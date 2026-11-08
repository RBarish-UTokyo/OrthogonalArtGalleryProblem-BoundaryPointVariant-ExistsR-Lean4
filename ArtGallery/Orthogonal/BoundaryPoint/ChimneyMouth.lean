module

public import ArtGallery.Orthogonal.BoundaryPoint.InverseGap

/-! # Visibility into a physical ceiling chimney
The selected tile meets the remainder only on its lower edge. Every line of
sight from below to the top intersects that lower edge. Its endpoints impose
two closed bounds on the visible interval of the top segment. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.ChimneyMouth
open Set RoomGrid RoomCoordinates RoomPolynomials GridParity PinGridData CorridorProgram Geometry

def coords (x y : Axis) (r : Rect Nat) : Rect P :=
  ((axisPolys x).getD r.1 [],(axisPolys x).getD r.2.1 [],
    (axisPolys y).getD r.2.2.1 [],(axisPolys y).getD r.2.2.2 [])

def notHigher (x y : Axis) (l r b t : ℚ) (m : Rect Nat) :=
  let c := coords x y m
  ltP c.2.1 [l] || (ltP [r] c.1 || (leP c.2.2.2 [b] || ltP [t] c.2.2.1))

def equalP (p : P) (q : ℚ) := (subP p [q]).all (fun a => decide (a=0))
def same (x y : Axis) (m : Rect Nat) (l r b t : ℚ) :=
  let c := coords x y m
  (equalP c.1 l && equalP c.2.1 r) && (equalP c.2.2.1 b && equalP c.2.2.2 t)
def check (x y : Axis) (ms : List (Rect Nat)) (m : Rect Nat) (l r b t : ℚ) :=
  same x y m l r b t && (rest m ms).all (notHigher x y l r b t)

noncomputable def upperX (g : Point) (u b t : ℝ) := g.1+(u-g.1)*(t-g.2)/(b-g.2)

private theorem eq_sound {p : P} {q : ℚ} (s : ℝ) (h : equalP p q=true) : evalR s p=(q:ℝ) := by
  have H := zero_sound h s
  simpa only [eval_sub,evalR,Rat.cast_zero,mul_zero,add_zero,sub_eq_zero] using H

private theorem cross_product {g z w : Point} (h : w∈ArtGallery.segment g z) :
    (w.1-g.1)*(z.2-g.2)=(z.1-g.1)*(w.2-g.2) := by
  rcases h with ⟨a,_,_,rfl⟩
  dsimp only; ring

theorem window {s : ℝ} (hs : 0<s) (hu : s≤1/65) {Q : Polygon} {x y : Axis}
    {ms : List (Rect Nat)} {m : Rect Nat} {l r b t : ℚ}
    (filled : Q.filled=cellsR (x.coordsR s) (y.coordsR s) ms) (hm : m∈ms)
    (pass : check x y ms m l r b t=true) (positive : (b:ℝ)<t) {g : Point} {X : ℝ}
    (below : g.2<b) (xl : (l:ℝ)≤X) (xr : X≤(r:ℝ)) (see : Q.Sees g (X,(t:ℝ))) :
    upperX g l b t≤X ∧ X≤upperX g r b t := by
  simp only [check,same,Bool.and_eq_true] at pass
  have L := eq_sound s pass.1.1.1
  have R := eq_sound s pass.1.1.2
  have B := eq_sound s pass.1.2.1
  have T := eq_sound s pass.1.2.2
  simp only [coords,index_value] at L R B T
  let F := tile (x.coordsR s) (y.coordsR s) m
  let H := cellsR (x.coordsR s) (y.coordsR s) (rest m ms)
  have split : Q.filled=F∪H := filled.trans (split_tile _ _ hm)
  have mem (w : Point) : w∈F ↔ (l:ℝ)≤w.1 ∧ w.1≤r ∧ (b:ℝ)≤w.2 ∧ w.2≤t := by
    simp only [F,tile,ChimneyRegion.cell,Set.mem_setOf_eq,L,R,B,T]
  have near : g∈H :=
    (split ▸ see (left_mem_segment ..)).resolve_left fun h => below.not_ge ((mem _).1 h).2.2.1
  have far : (X,(t:ℝ))∈F := (mem _).2 ⟨xl,xr,positive.le,le_rfl⟩
  have union : ArtGallery.segment g (X,(t:ℝ))⊆H∪F := by rw [Set.union_comm,← split]; exact see
  obtain ⟨w,seg,hw⟩ := SingleWindow.segment_meets_window (closed_tiles _ _ _)
    (ChimneyRegion.cell_closed _ _ _ _) near far union
  rcases (mem _).1 hw.2 with ⟨wl,wr,wb,wt⟩
  obtain ⟨k,hk,kl,kr,kb,kt⟩ := hw.1
  have hh := List.all_eq_true.mp pass.2 k hk
  simp only [notHigher,coords,Bool.or_eq_true] at hh
  have wy : w.2=(b:ℝ) := by
    rcases hh with left|right|bottom|top
    · have v := lt_sound hs hu left
      simp only [index_value,evalR,mul_zero,add_zero] at v
      exact (v.not_ge (wl.trans kr)).elim
    · have v := lt_sound hs hu right
      simp only [index_value,evalR,mul_zero,add_zero] at v
      exact (v.not_ge (kl.trans wr)).elim
    · have v := le_sound hs hu bottom
      simp only [index_value,evalR,mul_zero,add_zero] at v
      exact le_antisymm (kt.trans v) wb
    · have v := lt_sound hs hu top
      simp only [index_value,evalR,mul_zero,add_zero] at v
      exact (v.not_ge (kb.trans wt)).elim
  have line := cross_product seg
  change (w.1-g.1)*((t:ℝ)-g.2)=(X-g.1)*(w.2-g.2) at line
  rw [wy] at line
  have eq : X=upperX g w.1 b t := by
    unfold upperX
    field_simp [sub_ne_zero.mpr below.ne']
    linarith [line]
  have mono : Monotone (fun u => upperX g u b t) := by
    intro u v h
    dsimp [upperX]
    gcongr
    · exact sub_nonneg.mpr (below.trans positive).le
  rw [eq]
  exact ⟨mono wl,mono wr⟩

theorem gap {l r a b : ℝ} (ha : l≤a ∧ a≤r) (hb : l≤b ∧ b≤r)
    (all : ∀ X, l≤X → X≤r → a≤X ∨ X≤b) : a≤b := by
  by_contra! bad
  rcases all ((a+b)/2) (by linarith [ha.1,hb.1]) (by linarith [ha.2,hb.2]) with h|h <;> linarith

end ArtGallery.Orthogonal.BoundaryPoint.ChimneyMouth
end
