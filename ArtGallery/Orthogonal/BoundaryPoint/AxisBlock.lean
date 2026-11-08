module

public import ArtGallery.Orthogonal.BoundaryPoint.SupportingEdge
public import ArtGallery.Orthogonal.BoundaryPoint.SlotLines

/-! # Physical occlusion on an inverse room's critical axis

The solid quadrant can be approached through the adjacent open slab. Closedness
retains only the tiles reached from that side. A directed determinant test on
the four endpoint pairs excludes every such tile beyond the next free band. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.AxisBlock
open Set Geometry RoomCoordinates RoomPolynomials RoomGrid CorridorProgram RoomExclusion
open GridParity PinGridData SupportingEdge SlotLines ArtGallery.Orthogonal.Hard

structure Query where
  role : Nat
  corner : Pt
  axis : P
  bottom : P
  top : P
  increasing : Bool
  solidEast : Bool
  solidNorth : Bool

def Query.xside (q : Query) : Side := if q.solidEast then .east else .west
def Query.yside (q : Query) : Side := if q.solidNorth then .north else .south
def Query.ends (q : Query) : List Pt := [(q.axis,q.bottom),(q.axis,q.top)]

def ends (x y : Axis) (roles : List (List Index)) (i : Nat) : List Pt :=
  [polyNode x y (nodeAt roles i 1),polyNode x y (nodeAt roles i 2)]

def orientedSign (pos : Bool) (a b c : Pt) := if pos then oriented a b c else minus (oriented a b c)
def lengthwise (inc : Bool) (a b : P) := if inc then ltP a b else ltP b a
def precedes (inc : Bool) (a b : ℝ) := if inc then a<b else b<a
def signed (pos : Bool) : ℝ := if pos then 1 else -1

private theorem andParts {a b : Bool} (h : (a && b)=true) : a=true ∧ b=true := by
  simpa only [Bool.and_eq_true] using h

theorem before_value {s : ℝ} (hs : 0<s) (hu : s≤1/65) {a b : P} (d : Bool) (h : lengthwise d a b=true) :
    precedes d (evalR s a) (evalR s b) := by cases d <;> apply lt_sound hs hu h

theorem sign_value {s : ℝ} (hs : 0<s) (hu : s≤1/65) (pos : Bool) {a b c : Pt}
    (h : strict (orientedSign pos a b c)=true) : 0<signed pos*det (pt s a) (pt s b) (pt s c) := by
  have H := strict_sound hs hu h
  cases pos <;> simpa [orientedSign,signed,eval_oriented,eval_minus] using H

private theorem pair_lift {s : ℝ} (hs : 0<s) (hu : s≤1/65) (pos : Bool) {a b c d v : Pt}
    (h : [a,b].all (fun g => [c,d].all (fun z => strict (orientedSign pos g z v)))=true)
    {g z : Point} (hg : g∈ArtGallery.segment (pt s a) (pt s b)) (hz : z∈ArtGallery.segment (pt s c) (pt s d)) :
    0<signed pos*det g z (pt s v) := by
  apply CutHull.signed_hulls (A:={pt s a,pt s b}) (B:={pt s c,pt s d}) _ _
    _ (segment_eq_convexHull_pair _ _ ▸ hg) (segment_eq_convexHull_pair _ _ ▸ hz)
  intro u hU w hW
  have test (i) (hi : i∈[a,b]) (j) (hj : j∈[c,d]) :=
    sign_value hs hu pos (List.all_eq_true.mp (List.all_eq_true.mp h i hi) j hj)
  rcases hU with hU|hU <;> rcases hW with hW|hW <;>
    subst_vars <;> first | exact test _ (by simp) _ (by simp)

def dead (x y : Axis) (q : Query) (r : Rect Nat) :=
  leP (cap q.xside x y r) (level q.xside q.corner)

def other (y : Axis) (q : Query) (r : Rect Nat) : P :=
  (axisPolys y).getD (if q.solidNorth then r.2.2.1 else r.2.2.2) []

def clear (x y : Axis) (guards : List Pt) (q : Query) (r : Rect Nat) :=
  dead x y q r ||
    (ltP ((axisPolys x).getD r.2.1 []) q.corner.1 ||
    (ltP q.corner.1 ((axisPolys x).getD r.1 []) ||
    (leP (cap q.yside x y r) (level q.yside q.corner) ||
     guards.all fun g => q.ends.all fun z =>
       strict (orientedSign (q.increasing==q.solidNorth) g z (q.corner.1,other y q r)))))

def ok (x y : Axis) (rs : List (Rect Nat)) (roles : List (List Index)) (q : Query) :=
  let g := ends x y roles q.role
  lengthwise q.increasing q.corner.1 q.axis &&
    (g.all (fun a => lengthwise q.increasing a.1 q.corner.1) && rs.all (clear x y g q))

private theorem interp_lt {u v z : Point} {k : ℝ} {inc : Bool}
    (ha : precedes inc u.1 k) (hb : precedes inc v.1 k) (hz : z∈ArtGallery.segment u v) :
    precedes inc z.1 k := by
  obtain ⟨t,ht,hu,rfl⟩ := mem_segment_iff_lerp.mp hz
  cases inc <;> simp only [precedes,Bool.false_eq_true,ite_false,ite_true,lerp] at *
  · have h := lt_min ha hb
    nlinarith only [h,mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr (min_le_left u.1 v.1)),
      mul_nonneg ht (sub_nonneg.mpr (min_le_right u.1 v.1))]
  · have h := max_lt ha hb
    nlinarith only [h,mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr (le_max_left u.1 v.1)),
      mul_nonneg ht (sub_nonneg.mpr (le_max_right u.1 v.1))]

theorem height_det {g z : Point} (ne : g.1≠z.1) (c y : ℝ) :
    (SlabSight.height g.1 g.2 z.1 z.2 c-y)*(z.1-g.1) = -det g z (c,y) := by
  unfold SlabSight.height det
  dsimp only
  field_simp [sub_ne_zero.mpr ne.symm] <;> ring

private theorem far_gap {s : ℝ} (q : Query) (y : Axis) (r : Rect Nat) {g z : Point}
    (hc : precedes q.increasing g.1 z.1)
    (test : 0<signed (q.increasing==q.solidNorth)*det g z
      (evalR s q.corner.1, evalR s (other y q r))) :
    let Y := SlabSight.height g.1 g.2 z.1 z.2 (evalR s q.corner.1)
    ¬((y.coordsR s).getD r.2.2.1 0≤Y ∧ Y≤(y.coordsR s).getD r.2.2.2 0) := by
  dsimp only
  intro box
  cases hi : q.increasing <;> cases hn : q.solidNorth <;>
    simp only [precedes,hi,hn,other,Bool.false_eq_true,ite_true,ite_false,index_value] at hc test <;>
    norm_num [signed] at test <;> rw [← List.getD_eq_getElem?_getD] at test
  · have id := height_det (g:=g) (z:=z) hc.ne' (evalR s q.corner.1) ((y.coordsR s).getD r.2.2.2 0)
    nlinarith only [id,test,mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr box.2) (sub_nonpos.mpr hc.le)]
  · have id := height_det (g:=g) (z:=z) hc.ne' (evalR s q.corner.1) ((y.coordsR s).getD r.2.2.1 0)
    nlinarith only [id,test,mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr box.1) (sub_nonpos.mpr hc.le)]
  · have id := height_det (g:=g) (z:=z) hc.ne (evalR s q.corner.1) ((y.coordsR s).getD r.2.2.2 0)
    nlinarith only [id,test,mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr box.2) (sub_nonneg.mpr hc.le)]
  · have id := height_det (g:=g) (z:=z) hc.ne (evalR s q.corner.1) ((y.coordsR s).getD r.2.2.1 0)
    nlinarith only [id,test,mul_nonneg (sub_nonneg.mpr box.1) (sub_nonneg.mpr hc.le)]

private theorem slopes {g z c : Point} (inc north : Bool) (h1 : precedes inc g.1 c.1)
    (h2 : precedes inc c.1 z.1)
    (h : if north then SlabSight.height g.1 g.2 z.1 z.2 c.1 ≤ c.2 else c.2 ≤ SlabSight.height g.1 g.2 z.1 z.2 c.1) :
    if north then z.2≤rayY g c z.1 else rayY g c z.1≤z.2 := by
  have facts : 0<(c.1-g.1)/(z.1-g.1) ∧ c.1≠g.1 ∧ z.1≠g.1 := by
    cases inc <;> simp only [precedes,Bool.false_eq_true,ite_false,ite_true] at h1 h2
    · exact ⟨div_pos_of_neg_of_neg (sub_neg.mpr h1) (sub_neg.mpr (h2.trans h1)),h1.ne,(h2.trans h1).ne⟩
    · exact ⟨div_pos (sub_pos.mpr h1) (sub_pos.mpr (h1.trans h2)),h1.ne',(h1.trans h2).ne'⟩
  have id : SlabSight.height g.1 g.2 z.1 z.2 c.1-c.2 =
      (z.2-rayY g c z.1)*((c.1-g.1)/(z.1-g.1)) := by
    unfold SlabSight.height rayY
    field_simp [sub_ne_zero.mpr facts.2.1,sub_ne_zero.mpr facts.2.2] <;> ring
  cases north <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h ⊢
  · apply sub_nonneg.mp
    exact nonneg_of_mul_nonneg_left (id ▸ sub_nonneg.mpr h) facts.1
  · apply sub_nonpos.mp
    exact nonpos_of_mul_nonpos_left (id ▸ sub_nonpos.mpr h) facts.1

theorem sound {s : ℝ} (hs : 0<s) (hu : s≤1/65) {Q : Polygon} {x y : Axis}
    {rs : List (Rect Nat)} {roles : List (List Index)} {q : Query}
    (hf : Q.filled=cellsR (x.coordsR s) (y.coordsR s) rs) (check : ok x y rs roles q=true)
    {g z : Point}
    (hg : g∈ArtGallery.segment (pt s ((ends x y roles q.role).getD 0 ([],[])))
      (pt s ((ends x y roles q.role).getD 1 ([],[]))))
    (hz : z∈ArtGallery.segment (pt s (q.axis,q.bottom)) (pt s (q.axis,q.top)))
    (see : Q.Sees g z) :
    if q.solidNorth then z.2≤rayY g (pt s q.corner) z.1 else rayY g (pt s q.corner) z.1≤z.2 := by
  let a := polyNode x y (nodeAt roles q.role 1)
  let b := polyNode x y (nodeAt roles q.role 2)
  change g∈ArtGallery.segment (pt s a) (pt s b) at hg
  have ⟨after,tests⟩ := andParts check
  have ⟨guards,tiles⟩ := andParts tests
  have ord' (p) (h : p∈[a,b]) := before_value hs hu q.increasing (List.all_eq_true.mp guards p h)
  have front : precedes q.increasing g.1 (pt s q.corner).1 :=
    interp_lt (ord' a (by simp)) (ord' b (by simp)) hg
  have zx : z.1=evalR s q.axis := by
    obtain ⟨t,_,_,rfl⟩ := mem_segment_iff_lerp.mp hz
    simp [lerp,pt]
  have back : precedes q.increasing (pt s q.corner).1 z.1 := zx ▸ before_value hs hu q.increasing after
  let c := pt s q.corner
  let Y := SlabSight.height g.1 g.2 z.1 z.2 c.1
  let P₀ : Point := (c.1,Y)
  have ord : precedes q.increasing g.1 z.1 := by
    cases e : q.increasing <;> simp only [e,precedes,Bool.false_eq_true,ite_false,ite_true] at * <;> linarith
  have ne : g.1≠z.1 := by cases e : q.increasing <;> simp only [e,precedes,Bool.false_eq_true,ite_false,ite_true] at ord <;> first | exact ord.ne | exact ord.ne'
  have hseg : P₀∈ArtGallery.segment g z := by
    apply SlabSight.path ne _ false
    cases e : q.increasing <;> simp only [e,precedes,Bool.false_eq_true,ite_false,ite_true] at front back ord
    · rw [uIcc_of_ge ord.le]; exact ⟨back.le,front.le⟩
    · rw [uIcc_of_le ord.le]; exact ⟨front.le,back.le⟩
  let near := rs.filter fun r => !(dead x y q r)
  let R := cellsR (x.coordsR s) (y.coordsR s) near
  have join : ∀ p∈Q.filled,normal q.xside p≤normal q.xside P₀ ∨ p∈R := by
    rintro p hp
    rw [hf] at hp
    obtain ⟨r,hr,box⟩ := hp
    by_cases hd : dead x y q r=true
    · left
      have lim := le_sound hs hu hd
      rw [level_value] at lim
      have hh := (cap_bound s q.xside x y r box).trans lim
      cases h : q.solidEast <;> simpa [Query.xside,h,normal,P₀,c] using hh
    · right; exact ⟨r,List.mem_filter.mpr ⟨hr,by simpa using hd⟩,box⟩
  have next : ∃ e∈ArtGallery.segment g z,normal q.xside P₀<normal q.xside e := by
    cases hi : q.increasing <;> cases hx : q.solidEast <;>
      simp only [hi,precedes,Bool.false_eq_true,ite_false,ite_true] at front back
    all_goals first
      | exact ⟨g,left_mem_segment ..,by simpa [Query.xside,hx,normal,P₀,c] using front⟩
      | exact ⟨z,right_mem_segment ..,by simpa [Query.xside,hx,normal,P₀,c] using back⟩
  obtain ⟨e,he,dir⟩ := next
  have reaches : P₀∈R := by
    by_contra missing
    apply outward q.xside (closed_tiles ..) missing join dir
    exact (segment_subset_of_convex (s:=ArtGallery.segment g z) (segment_eq .. ▸ convex_segment ..) hseg he).trans see
  obtain ⟨r,hr,box⟩ := reaches
  obtain ⟨member,nearSide⟩ := List.mem_filter.mp hr
  have hh := List.all_eq_true.mp tiles r member
  change (dead x y q r || _)=true at hh
  rw [Bool.not_eq_true' _ |>.mp nearSide,Bool.false_or] at hh
  simp only [Bool.or_eq_true] at hh
  rcases hh with west|east|below|band
  · have h := lt_sound hs hu west; rw [index_value] at h
    exact (h.not_ge box.2.1).elim
  · have h := lt_sound hs hu east; rw [index_value] at h
    exact (h.not_ge box.1).elim
  · have lim := le_sound hs hu below
    rw [level_value] at lim
    have bound := (cap_bound s q.yside x y r box).trans lim
    apply slopes q.increasing q.solidNorth front back
    cases ht : q.solidNorth <;> simpa [Query.yside,ht,normal,P₀,c,Y] using bound
  · have sign := pair_lift hs hu (q.increasing==q.solidNorth) band hg hz
    exact (far_gap q y r ord sign box.2.2).elim

def margins (x y : Axis) (roles : List (List Index)) (q : Query) :=
  (ends x y roles q.role).all fun a =>
    lengthwise q.increasing a.1 q.corner.1 &&
    (strict (orientedSign q.increasing a (q.axis,q.bottom) q.corner) &&
     strict (orientedSign (!q.increasing) a (q.axis,q.top) q.corner))

theorem ray_det {g c : Point} (hn : c.1≠g.1) (t v : ℝ) :
    det g (t,v) c=(rayY g c t-v)*(c.1-g.1) := by
  unfold rayY det; dsimp only
  field_simp [sub_ne_zero.mpr hn] <;> ring

private theorem one_target {s : ℝ} (hs : 0<s) (hu : s≤1/65) (pos : Bool) {a b w c : Pt}
    (tests : ∀ j∈[a,b], strict (orientedSign pos j w c)=true) {g : Point}
    (hg : g∈ArtGallery.segment (pt s a) (pt s b)) : 0<signed pos*det g (pt s w) (pt s c) := by
  apply pair_lift hs hu pos (a:=a) (b:=b) (c:=w) (d:=w) _ hg (left_mem_segment ..)
  apply List.all_eq_true.mpr
  intro j hj
  simp [tests j hj]

theorem interior {s : ℝ} (hs : 0<s) (hu : s≤1/65) {x y : Axis}
    {roles : List (List Index)} {q : Query} (h : margins x y roles q=true)
    {g : Point} (hg : g∈ArtGallery.segment (pt s ((ends x y roles q.role).getD 0 ([],[])))
      (pt s ((ends x y roles q.role).getD 1 ([],[])))) :
    evalR s q.bottom < rayY g (pt s q.corner) (evalR s q.axis) ∧
      rayY g (pt s q.corner) (evalR s q.axis)< evalR s q.top := by
  let a := polyNode x y (nodeAt roles q.role 1)
  let b := polyNode x y (nodeAt roles q.role 2)
  change g∈ArtGallery.segment (pt s a) (pt s b) at hg
  have tests (j) (hm : j∈[a,b]) := andParts (List.all_eq_true.mp h j hm)
  have before (j) (hm : j∈[a,b]) := before_value hs hu q.increasing (tests j hm).1
  have bound := interp_lt (u:=pt s a) (v:=pt s b) (before a (by simp)) (before b (by simp)) hg
  have b1 := one_target hs hu q.increasing (fun j hj => (andParts (tests j hj).2).1) hg
  have b2 := one_target hs hu (!q.increasing) (fun j hj => (andParts (tests j hj).2).2) hg
  change 0<signed q.increasing*det g (evalR s q.axis,evalR s q.bottom) (pt s q.corner) at b1
  change 0<signed (!q.increasing)*det g (evalR s q.axis,evalR s q.top) (pt s q.corner) at b2
  change precedes q.increasing g.1 (pt s q.corner).1 at bound
  cases hdir : q.increasing <;> simp [hdir,precedes,signed] at bound b1 b2
  · rw [ray_det bound.ne] at b1 b2
    exact ⟨sub_pos.mp (pos_of_mul_neg_left b1 (sub_neg.mpr bound).le),
      sub_neg.mp (neg_of_mul_pos_left b2 (sub_neg.mpr bound).le)⟩
  · rw [ray_det bound.ne'] at b1 b2
    exact ⟨sub_pos.mp (pos_of_mul_pos_left b1 (sub_pos.mpr bound).le),
      sub_neg.mp (neg_of_mul_neg_left b2 (sub_pos.mpr bound).le)⟩

end ArtGallery.Orthogonal.BoundaryPoint.AxisBlock
end
