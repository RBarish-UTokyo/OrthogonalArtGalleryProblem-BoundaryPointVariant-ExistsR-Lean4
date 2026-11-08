module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomPolynomials
public import ArtGallery.Orthogonal.BoundaryPoint.GridParity
public import ArtGallery.Orthogonal.BoundaryPoint.CutHull
public import Mathlib.Analysis.Convex.Combination

/-! # Excluding a whole physical guard spot from an arithmetic box

A finite signed polynomial test certifies that the cut misses all occupied
rectangles and that every endpoint ray crosses the open gap. The result holds
uniformly in reciprocal gallery size and for every real point of both sets.
-/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomExclusion
open Set RoomGrid RoomCoordinates RoomPolynomials GridParity CorridorProgram ArtGallery.Orthogonal.Hard

structure Query where
  role : Nat
  target : Rect ℚ
  cut : ℚ
  low : ℚ
  high : ℚ

def nodeAt (roles : List (List Index)) (r j : Nat) := (roles.getD r []).getD j (0,0)

def corners (r : Rect ℚ) : List Pt :=
  [([r.1],[r.2.2.1]),([r.1],[r.2.2.2]),([r.2.1],[r.2.2.1]),([r.2.1],[r.2.2.2])]

def outside (x y : Axis) (q : Query) (r : Rect Nat) : Bool :=
  ltP ((axisPolys x).getD r.2.1 []) [q.cut] || ltP [q.cut] ((axisPolys x).getD r.1 []) ||
  leP ((axisPolys y).getD r.2.2.2 []) [q.low] || leP [q.high] ((axisPolys y).getD r.2.2.1 [])

def ok (x y : Axis) (rs : List (Rect Nat)) (roles : List (List Index)) (q : Query) : Bool :=
  let a := polyNode x y (nodeAt roles q.role 1)
  let b := polyNode x y (nodeAt roles q.role 2)
  decide (q.cut<q.target.1 ∧ q.target.1≤q.target.2.1 ∧ q.target.2.2.1≤q.target.2.2.2) &&
    (rs.all (outside x y q) && [a,b].all (fun g =>
      ltP g.1 [q.cut] && (corners q.target).all (fun v =>
      strict (minus (oriented g v ([q.cut],[q.low]))) && strict (oriented g v ([q.cut],[q.high])))))

private theorem literal (s : ℝ) (q : ℚ) : evalR s [q]=(q:ℝ) := by simp [evalR]

private theorem andParts {a b : Bool} (h : (a && b)=true) : a=true ∧ b=true := by
  simpa only [Bool.and_eq_true] using h

private theorem cut_free {s : ℝ} (hs : 0<s) (hu : s≤1/65) (x y : Axis) (q : Query)
    {rs : List (Rect Nat)} (h : rs.all (outside x y q)=true) {z : ℝ}
    (hl : (q.low:ℝ)<z) (hh : z<(q.high:ℝ)) :
    ((q.cut:ℝ),z)∉cellsR (x.coordsR s) (y.coordsR s) rs := by
  rintro ⟨r,hr,rx,Rx,ry,Ry⟩
  have tests := List.all_eq_true.mp h r hr
  simp only [outside,Bool.or_eq_true] at tests
  rcases tests with ((left|right)|low)|high
  · have hh := lt_sound hs hu left
    rw [index_value,literal] at hh
    exact hh.not_ge Rx
  · have hh := lt_sound hs hu right
    rw [index_value,literal] at hh
    exact hh.not_ge rx
  · have hy := le_sound hs hu low
    rw [index_value,literal] at hy
    exact hl.not_ge (Ry.trans hy)
  · have hy := le_sound hs hu high
    rw [index_value,literal] at hy
    exact hh.not_ge (hy.trans ry)

private theorem interval_hull (l r : ℝ) (h : l≤r) :
    Icc l r = convexHull ℝ ({l,r}:Set ℝ) := by
  rw [convexHull_pair,_root_.segment_eq_Icc h]

private theorem left_of_segment {a b p : Point} {c : ℝ} (ha : a.1<c) (hb : b.1<c)
    (hp : p∈ArtGallery.segment a b) : p.1<c := by
  obtain ⟨t,ht,hu,rfl⟩ := hp
  change a.1+t*(b.1-a.1)<c
  rcases le_total a.1 b.1 with le|le
  · linarith [mul_le_mul_of_nonneg_right hu (sub_nonneg.mpr le)]
  · linarith [mul_nonpos_of_nonneg_of_nonpos ht (sub_nonpos.mpr le)]

theorem sound {s : ℝ} (hs : 0<s) (hu : s≤1/65) {P : Polygon} {x y : Axis}
    {rs : List (Rect Nat)} {roles : List (List Index)} {q : Query}
    (hf : P.filled=cellsR (x.coordsR s) (y.coordsR s) rs) (check : ok x y rs roles q=true) :
    let f := gridPt (x.coordsR s) (y.coordsR s)
    ∀ g∈ArtGallery.segment (f (nodeAt roles q.role 1)) (f (nodeAt roles q.role 2)),
    ∀ z : Point, (q.target.1:ℝ)≤z.1 → z.1≤(q.target.2.1:ℝ) →
      (q.target.2.2.1:ℝ)≤z.2 → z.2≤(q.target.2.2.2:ℝ) → ¬P.Sees g z := by
  let a := polyNode x y (nodeAt roles q.role 1)
  let b := polyNode x y (nodeAt roles q.role 2)
  have ⟨ord,checks⟩ := andParts check
  have ⟨free,all⟩ := andParts checks
  obtain ⟨cOrder,xOrder,yOrder⟩ := of_decide_eq_true ord
  let A : Set Point := {pt s a,pt s b}
  let B : Set Point := ({(q.target.1:ℝ),(q.target.2.1:ℝ)}:Set ℝ) ×ˢ
    ({(q.target.2.2.1:ℝ),(q.target.2.2.2:ℝ)}:Set ℝ)
  have liftA {p : Point} (h : p∈A) : ∃ u∈[a,b],pt s u=p := by
    rcases h with h|h
    · exact ⟨a,by simp,h.symm⟩
    · exact ⟨b,by simp,h.symm⟩
  have liftB {p : Point} (h : p∈B) : ∃ u∈corners q.target,pt s u=p := by
    obtain ⟨hx,hy⟩ := h
    rcases hx with hx|hx <;> rcases hy with hy|hy
    all_goals first
      | exact ⟨([q.target.1],[q.target.2.2.1]),by simp [corners],Prod.ext ((literal _ _).trans hx.symm) ((literal _ _).trans hy.symm)⟩
      | exact ⟨([q.target.1],[q.target.2.2.2]),by simp [corners],Prod.ext ((literal _ _).trans hx.symm) ((literal _ _).trans hy.symm)⟩
      | exact ⟨([q.target.2.1],[q.target.2.2.1]),by simp [corners],Prod.ext ((literal _ _).trans hx.symm) ((literal _ _).trans hy.symm)⟩
      | exact ⟨([q.target.2.1],[q.target.2.2.2]),by simp [corners],Prod.ext ((literal _ _).trans hx.symm) ((literal _ _).trans hy.symm)⟩
  have east (u) (h : u∈[a,b]) : (pt s u).1<(q.cut:ℝ) := by
    have left := lt_sound hs hu (andParts (List.all_eq_true.mp all u h)).1
    simpa only [pt,literal] using left
  have sign (u) (h : u∈[a,b]) (v) (hv : v∈corners q.target) :
      0 < (-1:ℝ)*ArtGallery.det (pt s u) (pt s v) (q.cut,q.low) ∧
      0 < (1:ℝ)*ArtGallery.det (pt s u) (pt s v) (q.cut,q.high) := by
    obtain ⟨neg,pos⟩ := andParts (List.all_eq_true.mp (andParts (List.all_eq_true.mp all u h)).2 v hv)
    have h₁ := strict_sound hs hu neg
    have h₂ := strict_sound hs hu pos
    simp only [eval_minus,eval_oriented,pt,literal] at h₁ h₂
    exact ⟨by simpa only [neg_one_mul,pt] using h₁,by simpa only [one_mul,pt] using h₂⟩
  dsimp only
  intro g hg z zl zr zb zt
  have hg' : g∈ArtGallery.segment (pt s a) (pt s b) := by
    simpa only [a,b,node_value] using hg
  have inside : z∈convexHull ℝ B := by
    rw [show B= _ ×ˢ _ by rfl,convexHull_prod,← interval_hull _ _ (Rat.cast_le.mpr xOrder),
      ← interval_hull _ _ (Rat.cast_le.mpr yOrder)]
    exact ⟨⟨zl,zr⟩,zb,zt⟩
  apply CutHull.excludes (A:=A) (B:=B) (c:=(q.cut:ℝ)) (l:=(q.low:ℝ)) (r:=(q.high:ℝ))
    (fun v hl hh => hf ▸ cut_free hs hu x y q free hl hh)
  · intro u hu' v hv'
    obtain ⟨a,ha,rfl⟩ := liftA hu'
    obtain ⟨b,hb,rfl⟩ := liftB hv'
    exact (sign a ha b hb).1
  · intro u hu' v hv'
    obtain ⟨a,ha,rfl⟩ := liftA hu'
    obtain ⟨b,hb,rfl⟩ := liftB hv'
    exact (sign a ha b hb).2
  · exact Geometry.segment_eq_convexHull_pair _ _ ▸ hg'
  · exact inside
  · exact left_of_segment (east a (by simp)) (east b (by simp)) hg'
  · exact (Rat.cast_lt.mpr cOrder).trans_le zl

end ArtGallery.Orthogonal.BoundaryPoint.RoomExclusion
end
