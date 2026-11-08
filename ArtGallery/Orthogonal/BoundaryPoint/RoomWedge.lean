module

public import ArtGallery.Orthogonal.BoundaryPoint.SingleWindow
public import ArtGallery.Orthogonal.BoundaryPoint.CopyOutside
public import ArtGallery.Orthogonal.BoundaryPoint.RoomCoordinates
public import ArtGallery.Orthogonal.BoundaryPoint.GridParity

/-! # Foreign guards and the critical boxes of a joined room

A sightline from outside a room to a point of the room passes through the room's
window. If the guard, the window and the target are confined to rational boxes,
the collinearity identity `(g.y-q.y)(z.x-q.x)=(q.x-g.x)(q.y-z.y)` of three
ordered points of a segment gives a contradiction whenever the two products have
disjoint interval enclosures. A guard of the rest of the polygon first crosses the
door, which is again such a box. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomWedge
open Set RoomCoordinates MarginCert ArtGallery.Orthogonal.Hard

/-- A closed rational box `[x0,x1]×[y0,y1]`. -/
abbrev QBox := ℚ × ℚ × ℚ × ℚ

def QBox.Mem (b : QBox) (p : Point) : Prop :=
  (b.1:ℝ)≤p.1 ∧ p.1≤(b.2.1:ℝ) ∧ (b.2.2.1:ℝ)≤p.2 ∧ p.2≤(b.2.2.2:ℝ)

def pLo (a0 a1 b0 b1 : ℚ) : ℚ := min (min (a0*b0) (a0*b1)) (min (a1*b0) (a1*b1))
def pHi (a0 a1 b0 b1 : ℚ) : ℚ := max (max (a0*b0) (a0*b1)) (max (a1*b0) (a1*b1))

private theorem lin {A B b0 b1 : ℝ} (h0 : b0≤B) (h1 : B≤b1) :
    min (A*b0) (A*b1)≤A*B ∧ A*B≤max (A*b0) (A*b1) := by
  rcases le_total 0 A with hA|hA
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h0 hA),
      (mul_le_mul_of_nonneg_left h1 hA).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h1 hA),
      (mul_le_mul_of_nonpos_left h0 hA).trans (le_max_left _ _)⟩

theorem mul_mem {A B : ℝ} {a0 a1 b0 b1 : ℚ} (ha0 : (a0:ℝ)≤A) (ha1 : A≤a1) (hb0 : (b0:ℝ)≤B) (hb1 : B≤b1) :
    (pLo a0 a1 b0 b1:ℝ)≤A*B ∧ A*B≤(pHi a0 a1 b0 b1:ℝ) := by
  obtain ⟨l,u⟩ := lin (A:=A) hb0 hb1
  obtain ⟨l0,u0⟩ := lin (A:=(b0:ℝ)) ha0 ha1
  obtain ⟨l1,u1⟩ := lin (A:=(b1:ℝ)) ha0 ha1
  simp only [pLo,pHi]; push_cast
  constructor
  · refine le_trans ?_ l
    rw [mul_comm A,mul_comm A] at *
    refine le_min ?_ ?_
    · refine le_trans ?_ l0
      rw [mul_comm (b0:ℝ),mul_comm (b0:ℝ)]
      exact le_min ((min_le_left _ _).trans (min_le_left _ _)) ((min_le_right _ _).trans (min_le_left _ _))
    · refine le_trans ?_ l1
      rw [mul_comm (b1:ℝ),mul_comm (b1:ℝ)]
      exact le_min ((min_le_left _ _).trans (min_le_right _ _)) ((min_le_right _ _).trans (min_le_right _ _))
  · refine le_trans u ?_
    rw [mul_comm A,mul_comm A] at *
    refine max_le ?_ ?_
    · refine le_trans u0 ?_
      rw [mul_comm (b0:ℝ),mul_comm (b0:ℝ)]
      exact max_le ((le_max_left _ _).trans (le_max_left _ _)) ((le_max_left _ _).trans (le_max_right _ _))
    · refine le_trans u1 ?_
      rw [mul_comm (b1:ℝ),mul_comm (b1:ℝ)]
      exact max_le ((le_max_right _ _).trans (le_max_left _ _)) ((le_max_right _ _).trans (le_max_right _ _))

/-- Disjoint enclosures of `(g.y-q.y)(z.x-q.x)` and `(q.x-g.x)(q.y-z.y)`. -/
def sep (g q z : QBox) : Bool :=
  let A0 := g.2.2.1-q.2.2.2; let A1 := g.2.2.2-q.2.2.1
  let B0 := z.1-q.2.1; let B1 := z.2.1-q.1
  let C0 := q.1-g.2.1; let C1 := q.2.1-g.1
  let D0 := q.2.2.1-z.2.2.2; let D1 := q.2.2.2-z.2.2.1
  decide (pHi A0 A1 B0 B1<pLo C0 C1 D0 D1 ∨ pHi C0 C1 D0 D1<pLo A0 A1 B0 B1)

theorem identity {g z q : Point} (hq : q∈ArtGallery.segment g z) :
    (g.2-q.2)*(z.1-q.1)=(q.1-g.1)*(q.2-z.2) := by
  obtain ⟨t,-,-,rfl⟩ := hq
  simp only; ring

theorem sep_sound {g q z : QBox} (h : sep g q z=true) {a b c : Point} (ha : g.Mem a) (hb : q.Mem b)
    (hc : z.Mem c) (hseg : b∈ArtGallery.segment a c) : False := by
  have e := identity hseg
  obtain ⟨a0,a1,a2,a3⟩ := ha
  obtain ⟨b0,b1,b2,b3⟩ := hb
  obtain ⟨c0,c1,c2,c3⟩ := hc
  have AB := mul_mem (A:=a.2-b.2) (B:=c.1-b.1) (a0:=g.2.2.1-q.2.2.2) (a1:=g.2.2.2-q.2.2.1)
    (b0:=z.1-q.2.1) (b1:=z.2.1-q.1) (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith)
  have CD := mul_mem (A:=b.1-a.1) (B:=b.2-c.2) (a0:=q.1-g.2.1) (a1:=q.2.1-g.1)
    (b0:=q.2.2.1-z.2.2.2) (b1:=q.2.2.2-z.2.2.1) (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith)
  simp only [sep,decide_eq_true_eq] at h
  rcases h with h|h
  · have := (Rat.cast_lt (K:=ℝ)).mpr h; linarith [AB.2,CD.1]
  · have := (Rat.cast_lt (K:=ℝ)).mpr h; linarith [AB.1,CD.2]

/-- The convex hull of two boxes. -/
def hull (a b : QBox) : QBox := (min a.1 b.1,max a.2.1 b.2.1,min a.2.2.1 b.2.2.1,max a.2.2.2 b.2.2.2)

theorem hull_mem {a b : QBox} {p q : Point} (hp : a.Mem p) (hq : b.Mem q) :
    ∀ r∈ArtGallery.segment p q, (hull a b).Mem r := by
  rintro r ⟨t,t0,t1,rfl⟩
  obtain ⟨p0,p1,p2,p3⟩ := hp
  obtain ⟨q0,q1,q2,q3⟩ := hq
  simp only [hull,QBox.Mem]; push_cast
  have m0 := min_le_left (a.1:ℝ) b.1; have m1 := min_le_right (a.1:ℝ) b.1
  have M0 := le_max_left (a.2.1:ℝ) b.2.1; have M1 := le_max_right (a.2.1:ℝ) b.2.1
  have n0 := min_le_left (a.2.2.1:ℝ) b.2.2.1; have n1 := min_le_right (a.2.2.1:ℝ) b.2.2.1
  have N0 := le_max_left (a.2.2.2:ℝ) b.2.2.2; have N1 := le_max_right (a.2.2.2:ℝ) b.2.2.2
  have e1 : p.1+t*(q.1-p.1)=(1-t)*p.1+t*q.1 := by ring
  have e2 : p.2+t*(q.2-p.2)=(1-t)*p.2+t*q.2 := by ring
  rw [e1,e2]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [mul_nonneg t0 (sub_nonneg.2 t1)]

section Window
variable {P : Polygon} {C R K : Set Point}

/-- The geometry of a joined room: the polygon is `(C ∪ R) ∪ K` for closed cells `C`, room `R`
and rest `K`; the window `C ∩ R` and the door `(C ∪ R) ∩ K` lie in boxes, and the room lies to the
right of the door box. -/
structure Frame (P : Polygon) (C R K : Set Point) (win door : QBox) (xmin : ℚ) : Prop where
  fill : P.filled=(C∪R)∪K
  closedC : IsClosed C
  closedR : IsClosed R
  closedK : IsClosed K
  window : ∀ p∈C∩R, win.Mem p
  doorIn : ∀ p∈(C∪R)∩K, door.Mem p
  roomX : ∀ p∈R, (xmin:ℝ)≤p.1
  doorX : door.2.1<xmin

theorem Frame.through {win door : QBox} {xmin : ℚ} (F : Frame P C R K win door xmin)
    {g z : Point} {gb zb : QBox} (hg : g∈P.filled) (hgR : g∉R) (hgb : gb.Mem g)
    (hz : z∈R) (hzb : zb.Mem z) (hsep : sep gb win zb=true) : ¬P.Sees g z := by
  intro sees
  have hg' : g∈C∪K := by
    rw [F.fill] at hg
    rcases hg with (h|h)|h
    · exact Or.inl h
    · exact absurd h hgR
    · exact Or.inr h
  have hall : ArtGallery.segment g z⊆(C∪K)∪R := by
    intro p hp
    have := sees hp
    rw [F.fill] at this
    rcases this with (h|h)|h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  obtain ⟨q,hq,hqC|hqK,hqR⟩ := SingleWindow.segment_meets_window (F.closedC.union F.closedK) F.closedR hg' hz hall
  · exact sep_sound hsep hgb (F.window q ⟨hqC,hqR⟩) hzb hq
  · have hd := F.doorIn q ⟨Or.inr hqR,hqK⟩
    have hx := F.roomX q hqR
    have := (Rat.cast_lt (K:=ℝ)).mpr F.doorX
    linarith [hd.2.1]

theorem Frame.from_rest {win door : QBox} {xmin : ℚ} (F : Frame P C R K win door xmin)
    {g z : Point} (hg : g∈K) (hz : z∈R) {zb : QBox} (hzb : zb.Mem z) (hsep : sep door win zb=true) :
    ¬P.Sees g z := by
  intro sees
  have hall : ArtGallery.segment g z⊆K∪(C∪R) := by
    intro p hp
    have := sees hp
    rw [F.fill] at this
    rcases this with h|h
    · exact Or.inr h
    · exact Or.inl h
  obtain ⟨q,hq,hqK,hqL⟩ := SingleWindow.segment_meets_window F.closedK (F.closedC.union F.closedR) hg
    (Or.inr hz) hall
  have hd := F.doorIn q ⟨hqL,hqK⟩
  have qR : q∉R := by
    intro h
    have hx := F.roomX q h
    have := (Rat.cast_lt (K:=ℝ)).mpr F.doorX
    linarith [hd.2.1]
  exact F.through (sees hq) qR hd hz hzb hsep ((CopyOutside.sub_segment hq).trans sees)

end Window

/-! ## Interval bounds of polynomial coordinate lines -/

def upper : List ℚ → ℚ
  | [] => 0
  | a::p => a+max 0 (upper p/65)

theorem le_upper (p : List ℚ) {s : ℝ} (hs : 0≤s) (hu : s≤1/65) : evalR s p≤(upper p:ℝ) := by
  induction p with
  | nil => simp [upper,evalR]
  | cons a p ih =>
    simp only [upper,evalR,Rat.cast_add,Rat.cast_max,Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat]
    apply add_le_add le_rfl
    apply le_trans (mul_le_mul_of_nonneg_left ih hs)
    by_cases h : 0≤(upper p:ℝ)
    · apply le_trans _ (le_max_right _ _)
      have hm := mul_le_mul_of_nonneg_right hu h
      linarith
    · exact (mul_nonpos_of_nonneg_of_nonpos hs (le_of_not_ge h)).trans (le_max_left _ _)

def gapLo (g : Gap) : ℚ := if g.order=0 then lower g.coefficients else min 0 ((1/65)^g.order*lower g.coefficients)
def gapHi (g : Gap) : ℚ := if g.order=0 then upper g.coefficients else max 0 ((1/65)^g.order*upper g.coefficients)

theorem gap_bounds (g : Gap) {s : ℝ} (hs : 0≤s) (hu : s≤1/65) :
    (gapLo g:ℝ)≤g.valR s ∧ g.valR s≤(gapHi g:ℝ) := by
  have l := lower_le g.coefficients hs hu
  have h := le_upper g.coefficients hs hu
  unfold gapLo gapHi Gap.valR
  split
  · rename_i h0; rw [h0,pow_zero,one_mul]; exact ⟨l,h⟩
  · rename_i h0
    have p0 : 0≤s^g.order := pow_nonneg hs _
    have p1 : s^g.order≤(1/65)^g.order := pow_le_pow_left₀ hs hu _
    have v1 : s^g.order*(lower g.coefficients:ℝ)≤s^g.order*evalR s g.coefficients := mul_le_mul_of_nonneg_left l p0
    have v2 : s^g.order*evalR s g.coefficients≤s^g.order*(upper g.coefficients:ℝ) := mul_le_mul_of_nonneg_left h p0
    push_cast
    constructor
    · rcases le_total 0 (lower g.coefficients:ℝ) with c|c
      · exact (min_le_left _ _).trans (le_trans (mul_nonneg p0 c) v1)
      · exact (min_le_right _ _).trans (le_trans (mul_le_mul_of_nonpos_right p1 c) v1)
    · rcases le_total 0 (upper g.coefficients:ℝ) with c|c
      · exact le_trans v2 ((mul_le_mul_of_nonneg_right p1 c).trans (le_max_right _ _))
      · exact le_trans v2 ((mul_nonpos_of_nonneg_of_nonpos p0 c).trans (le_max_left _ _))

def coordLo (a : Axis) (k : Nat) : ℚ := lower a.initial+((a.gaps.take k).map gapLo).sum
def coordHi (a : Axis) (k : Nat) : ℚ := upper a.initial+((a.gaps.take k).map gapHi).sum

theorem positions_getD (f : Gap → ℝ) : ∀ (gs : List Gap) (z : ℝ) (k : Nat), k≤gs.length →
    (positions f z gs).getD k 0=z+((gs.take k).map f).sum
  | [], z, 0, _ => by simp [positions]
  | [], z, k+1, h => by simp at h
  | g::gs, z, 0, _ => by simp [positions]
  | g::gs, z, k+1, h => by
    simp only [positions,List.getD_cons_succ,List.take_succ_cons,List.map_cons,List.sum_cons]
    rw [positions_getD f gs (z+f g) k (by simpa using h)]; ring

theorem sum_bounds {s : ℝ} (hs : 0≤s) (hu : s≤1/65) : ∀ l : List Gap,
    (((l.map gapLo).sum:ℚ):ℝ)≤(l.map (fun g => g.valR s)).sum ∧
      (l.map (fun g => g.valR s)).sum≤(((l.map gapHi).sum:ℚ):ℝ)
  | [] => by simp
  | g::l => by
    have ih := sum_bounds hs hu l
    have b := gap_bounds g hs hu
    simp only [List.map_cons,List.sum_cons,Rat.cast_add]
    constructor <;> linarith [ih.1,ih.2,b.1,b.2]

theorem coord_bounds (a : Axis) {k : Nat} (hk : k≤a.gaps.length) {s : ℝ} (hs : 0≤s) (hu : s≤1/65) :
    (coordLo a k:ℝ)≤(a.coordsR s).getD k 0 ∧ (a.coordsR s).getD k 0≤(coordHi a k:ℝ) := by
  rw [Axis.coordsR,positions_getD _ _ _ _ hk]
  have l := lower_le a.initial hs hu
  have h := le_upper a.initial hs hu
  have b := sum_bounds hs hu (a.gaps.take k)
  simp only [coordLo,coordHi,Rat.cast_add]
  constructor <;> linarith [b.1,b.2]

/-- The box of a grid node of two polynomial axes. -/
def gridBox (a b : Axis) (p : Nat × Nat) : QBox := (coordLo a p.1,coordHi a p.1,coordLo b p.2,coordHi b p.2)

theorem gridBox_mem (a b : Axis) {p : Nat × Nat} (h1 : p.1≤a.gaps.length) (h2 : p.2≤b.gaps.length)
    {s : ℝ} (hs : 0≤s) (hu : s≤1/65) : (gridBox a b p).Mem (gridPt (a.coordsR s) (b.coordsR s) p) := by
  have x := coord_bounds a h1 hs hu
  have y := coord_bounds b h2 hs hu
  exact ⟨x.1,x.2,y.1,y.2⟩

/-- The rectangles of a room lie right of `xmin`. -/
theorem cells_left (a b : Axis) (cs : List (Nat × Nat × Nat × Nat)) (xmin : ℚ)
    (h : cs.all (fun r => decide (r.1≤a.gaps.length ∧ xmin≤coordLo a r.1))=true) {s : ℝ} (hs : 0≤s) (hu : s≤1/65) :
    ∀ p∈GridParity.cellsR (a.coordsR s) (b.coordsR s) cs, (xmin:ℝ)≤p.1 := by
  rintro p ⟨r,hr,h1,-⟩
  have hh := List.all_eq_true.mp h r hr
  simp only [decide_eq_true_eq] at hh
  have cb := coord_bounds a hh.1 hs hu
  have := (Rat.cast_le (K:=ℝ)).mpr hh.2
  linarith [cb.1]

theorem size_bounds {n : Nat} (hn : 65≤n) : 0≤1/(n:ℝ) ∧ 1/(n:ℝ)≤1/65 := by
  have h : (65:ℝ)≤n := by exact_mod_cast hn
  exact ⟨by positivity,one_div_le_one_div_of_le (by norm_num) h⟩

/-! ## Interval bounds of straight-line registers -/

open MarginCert in
theorem exec_encloses {args : List Box} {v : List ℝ} (hv : Encloses args v) :
    ∀ (rs : List Row) {bs : List Box} {vs : List ℝ}, Encloses bs vs → ok args bs rs=true →
      Encloses (stack bs rs) (execReal v vs rs)
  | [], _, _, hs, _ => hs
  | r::rest, bs, vs, hs, h => by
    simp only [ok,Bool.and_eq_true] at h
    obtain ⟨⟨hop,-⟩,hrest⟩ := h
    exact exec_encloses hv rest (hs.cons (Op.sound hv hs hop)) hrest

theorem stack_append (bs : List Box) : ∀ a b : List Row, stack bs (a++b)=stack (stack bs a) b
  | [], _ => rfl
  | r::a, b => stack_append (r.bound::bs) a b

theorem execRat_append (args : List ℚ) : ∀ (xs : List ℚ) (a b : List MarginCert.Row),
    execRat args (execRat args xs a) b=execRat args xs (a++b)
  | _, [], _ => rfl
  | _, _::a, b => execRat_append args _ a b

theorem cast_get (xs : List ℚ) (i : Nat) :
    (getRat xs i:ℝ)=MarginCert.getReal (xs.map (fun x : ℚ => (x:ℝ))) i := by
  unfold getRat MarginCert.getReal
  rw [List.getElem?_map]
  cases xs[i]? <;> simp

open MarginCert in
/-- Every register of a checked program lies in its certified box. -/
theorem register_box {args : List Box} {a : List ℚ} (hv : Encloses args (a.map (fun q : ℚ => (q:ℝ))))
    {rs : List Row} (h : ok args [] rs=true) (j : Nat) :
    (getBox (stack [] rs) j).Mem (getRat (execRat a [] rs) j:ℝ) := by
  have e := exec_encloses hv rs (bs:=[]) (vs:=[]) (fun i => by simp [getBox,getReal,zeroBox,Box.Mem]) h j
  rw [cast_get,cast_exec]; simpa using e

end ArtGallery.Orthogonal.BoundaryPoint.RoomWedge
end
