module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomExclusion
public import ArtGallery.Orthogonal.BoundaryPoint.PinGridData

/-! # The exterior side of an orthogonal supporting edge
For every rectangle, the certificate either puts it behind the guard's
supporting line or separates it strictly from the entire allowed segment.
Finiteness and closedness keep sufficiently short outward rays in the exterior. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SupportingEdge
open Set Filter Topology Geometry RoomCoordinates RoomPolynomials RoomGrid CorridorProgram
open GridParity RoomExclusion PinGridData ArtGallery.Orthogonal.Hard

inductive Side | west | east | south | north deriving DecidableEq

private theorem andParts {a b : Bool} (h : (a && b)=true) : a=true ∧ b=true := by
  simpa only [Bool.and_eq_true] using h

def allSides : List Side := [.west,.east,.south,.north]

def normal (d : Side) (p : Point) : ℝ :=
  match d with | .west => -p.1 | .east => p.1 | .south => -p.2 | .north => p.2

def level (d : Side) (p : Pt) : P :=
  match d with | .west => minus p.1 | .east => p.1 | .south => minus p.2 | .north => p.2

def cap (d : Side) (x y : Axis) (r : Rect Nat) : P :=
  match d with
  | .west => minus ((axisPolys x).getD r.1 [])
  | .east => (axisPolys x).getD r.2.1 []
  | .south => minus ((axisPolys y).getD r.2.2.1 [])
  | .north => (axisPolys y).getD r.2.2.2 []

theorem level_value (s : ℝ) (d : Side) (p : Pt) :
    evalR s (level d p)=normal d (pt s p) := by cases d <;> simp [level,pt,normal,eval_minus]

theorem cap_bound (s : ℝ) (d : Side) (x y : Axis) (r : Rect Nat) {p : Point}
    (hp : p ∈ tile (x.coordsR s) (y.coordsR s) r) : normal d p≤evalR s (cap d x y r) := by
  rcases hp with ⟨xl,xh,yl,yh⟩
  cases d <;> simp only [normal,cap,eval_minus,index_value,neg_le_neg_iff] <;> assumption

theorem normal_lerp (d : Side) (a b : Point) (t : ℝ) :
    normal d (lerp a b t)=normal d a+t*(normal d b-normal d a) := by
  cases d <;> simp only [lerp,normal] <;> ring

private theorem lower {a b g : Point} (d : Side) {k : ℝ} (ha : k≤normal d a) (hb : k≤normal d b)
    (hg : g∈ArtGallery.segment a b) : k≤normal d g := by
  obtain ⟨t,ht,hu,rfl⟩ := mem_segment_iff_lerp.mp hg
  rw [normal_lerp]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr ha),mul_nonneg ht (sub_nonneg.mpr hb)]

private theorem lower_strict {a b g : Point} (d : Side) {k : ℝ} (ha : k<normal d a) (hb : k<normal d b)
    (hg : g∈ArtGallery.segment a b) : k<normal d g :=
  (lt_min ha hb).trans_le (lower d (min_le_left ..) (min_le_right ..) hg)

def behind (x y : Axis) (a b : Pt) (d : Side) (r : Rect Nat) :=
  leP (cap d x y r) (level d a) && leP (cap d x y r) (level d b)

def away (x y : Axis) (a b : Pt) (r : Rect Nat) :=
  allSides.any fun d => ltP (cap d x y r) (level d a) && ltP (cap d x y r) (level d b)

def ok (x y : Axis) (rs : List (Rect Nat)) (roles : List (List Index)) (i : Nat) (d : Side) :=
  let a := polyNode x y (nodeAt roles i 1)
  let b := polyNode x y (nodeAt roles i 2)
  rs.all fun r => behind x y a b d r || away x y a b r

theorem outward {Q : Polygon} {bad : Set Point} {g z : Point} (d : Side)
    (closed : IsClosed bad) (hbad : g∉bad)
    (support : ∀ p∈Q.filled, normal d p≤normal d g ∨ p∈bad)
    (hz : normal d g<normal d z) : ¬Q.Sees g z := by
  intro seen
  have cont : Continuous (lerp g z) := by unfold lerp; fun_prop
  have tend : Tendsto (lerp g z) (𝓝[>] (0:ℝ)) (𝓝 g) := by
    simpa using (cont.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  apply hbad (closed.mem_of_tendsto tend ?_)
  have le1 : ∀ᶠ t : ℝ in 𝓝[>] 0, t<1 :=
    (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,le1] with t ht hu
  have pos : 0<t := ht
  have beyond : normal d g<normal d (lerp g z t) := by
    rw [normal_lerp]; linarith only [mul_pos pos (sub_pos.mpr hz)]
  exact (support _ (seen (lerp_mem_segment g z pos.le hu.le))).resolve_left beyond.not_ge

theorem sound {s : ℝ} (hs : 0<s) (hu : s≤1/65) {Q : Polygon} {x y : Axis}
    {rs : List (Rect Nat)} {roles : List (List Index)} {i : Nat} {d : Side}
    (filled : Q.filled=cellsR (x.coordsR s) (y.coordsR s) rs) (check : ok x y rs roles i d=true) :
    let f := gridPt (x.coordsR s) (y.coordsR s)
    ∀ g∈ArtGallery.segment (f (nodeAt roles i 1)) (f (nodeAt roles i 2)),
    ∀ z, normal d g<normal d z → ¬Q.Sees g z := by
  let a := polyNode x y (nodeAt roles i 1)
  let b := polyNode x y (nodeAt roles i 2)
  let far := rs.filter fun r => !(behind x y a b d r)
  dsimp only
  intro g hg z hz
  have spot : g∈ArtGallery.segment (pt s a) (pt s b) := by simpa only [a,b,node_value] using hg
  apply outward (bad:=cellsR (x.coordsR s) (y.coordsR s) far) d (closed_tiles ..) _ _ hz
  · rintro ⟨r,hr,box⟩
    obtain ⟨member,neg⟩ := List.mem_filter.mp hr
    have both := List.all_eq_true.mp check r member
    change (behind x y a b d r || away x y a b r)=true at both
    have no : behind x y a b d r=false := Bool.not_eq_true' _ |>.mp neg
    rw [no,Bool.false_or] at both
    obtain ⟨k,_,two⟩ := List.any_eq_true.mp both
    obtain ⟨left,right⟩ := andParts two
    have A := lt_sound hs hu left
    have B := lt_sound hs hu right
    rw [level_value] at A B
    exact (lower_strict k A B spot).not_ge (cap_bound s k x y r box)
  · intro p hp
    rw [filled] at hp
    obtain ⟨r,mem,box⟩ := hp
    by_cases hh : behind x y a b d r=true
    · obtain ⟨left,right⟩ := andParts hh
      have A := le_sound hs hu left
      have B := le_sound hs hu right
      rw [level_value] at A B
      exact Or.inl ((cap_bound s d x y r box).trans (lower d A B spot))
    · exact Or.inr ⟨r,List.mem_filter.mpr ⟨mem,by simpa using hh⟩,box⟩

def levelTest (x y : Axis) (roles : List (List Index)) (i : Nat) (d : Side) (bound : P) :=
  [1,2].all fun j => leP (level d (polyNode x y (nodeAt roles i j))) bound

theorem excludes_above {s : ℝ} (hs : 0<s) (hu : s≤1/65) {Q : Polygon} {x y : Axis}
    {rs : List (Rect Nat)} {roles : List (List Index)} {i : Nat} {d : Side} {bound : P}
    (filled : Q.filled=cellsR (x.coordsR s) (y.coordsR s) rs) (check : ok x y rs roles i d=true)
    (capTest : levelTest x y roles i d bound=true) :
    let f := gridPt (x.coordsR s) (y.coordsR s)
    ∀ g∈ArtGallery.segment (f (nodeAt roles i 1)) (f (nodeAt roles i 2)),
    ∀ z, evalR s bound<normal d z → ¬Q.Sees g z := by
  dsimp only
  intro g hg z hz
  apply sound hs hu filled check g hg z
  apply lt_of_le_of_lt _ hz
  have endpoint (j : Nat) (h : j∈[1,2]) := le_sound hs hu (List.all_eq_true.mp capTest j h)
  have ha := endpoint 1 (by simp)
  have hb := endpoint 2 (by simp)
  rw [level_value,node_value] at ha hb
  obtain ⟨t,ht,hu,rfl⟩ := mem_segment_iff_lerp.mp hg
  rw [normal_lerp]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr ha), mul_nonneg ht (sub_nonneg.mpr hb)]

end ArtGallery.Orthogonal.BoundaryPoint.SupportingEdge
end
