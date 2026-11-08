module

public import ArtGallery.Orthogonal.BoundaryPoint.SepCert
public import ArtGallery.Orthogonal.BoundaryPoint.CellRoles

/-! # A guard segment sees a whole closed grid cell through a chain of tiles

A certificate lists tiles `R₀, …, Rₘ` of the chart: the guard segment lies in `R₀`, the target
cell in `Rₘ`, and consecutive tiles share a window on a grid line. Every sightline from the guard
segment to the cell crosses each window: the determinant of the sightline with each window end
has a certified weak sign at the eight pairs of a guard end and a cell corner, hence everywhere
(it is affine in the guard and in the target). The parameters of a sightline in consecutive tiles
form overlapping closed intervals, which cover `[0,1]`; so the sightline lies in the region. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CoverChain
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert RegisterForm MarginCert ArtGallery.Orthogonal.Hard

/-! ## Real geometry -/

/-- A closed axis rectangle. -/
def Rect (x₀ x₁ y₀ y₁ : ℝ) : Set Point := {p | x₀≤p.1 ∧ p.1≤x₁ ∧ y₀≤p.2 ∧ p.2≤y₁}

theorem rect_convex (x₀ x₁ y₀ y₁ : ℝ) : Convex ℝ (Rect x₀ x₁ y₀ y₁) := by
  intro p hp q hq a b ha hb hab
  obtain ⟨p0,p1,p2,p3⟩ := hp
  obtain ⟨q0,q1,q2,q3⟩ := hq
  simp only [Rect,Set.mem_setOf_eq,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  obtain rfl : b=1-a := by linarith
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [mul_nonneg ha (sub_nonneg.2 p0),mul_nonneg hb (sub_nonneg.2 q0),
    mul_nonneg ha (sub_nonneg.2 p1),mul_nonneg hb (sub_nonneg.2 q1),mul_nonneg ha (sub_nonneg.2 p2),
    mul_nonneg hb (sub_nonneg.2 q2),mul_nonneg ha (sub_nonneg.2 p3),mul_nonneg hb (sub_nonneg.2 q3)]

theorem lerp_rect {x₀ x₁ y₀ y₁ : ℝ} {p q : Point} (hp : p∈Rect x₀ x₁ y₀ y₁) (hq : q∈Rect x₀ x₁ y₀ y₁)
    {t : ℝ} (t0 : 0≤t) (t1 : t≤1) : Geometry.lerp p q t∈Rect x₀ x₁ y₀ y₁ := by
  obtain ⟨p0,p1,p2,p3⟩ := hp
  obtain ⟨q0,q1,q2,q3⟩ := hq
  simp only [Rect,Geometry.lerp,Set.mem_setOf_eq]
  have e1 : p.1+t*(q.1-p.1)=(1-t)*p.1+t*q.1 := by ring
  have e2 : p.2+t*(q.2-p.2)=(1-t)*p.2+t*q.2 := by ring
  rw [e1,e2]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [mul_nonneg t0 (sub_nonneg.2 t1)]

/-- A finite chain of convex sets with consecutive overlaps has a preconnected union. -/
theorem chain_preconnected : ∀ (l : List (Set ℝ)), (∀ S∈l, Convex ℝ S) →
    l.IsChain (fun S T => (S∩T).Nonempty) → IsPreconnected (⋃ S∈l, S)
  | [],_,_ => by
    have e : (⋃ S∈([]:List (Set ℝ)), S)=∅ := by ext; simp
    rw [e]; exact isPreconnected_empty
  | [S],hc,_ => by simpa using (hc S (by simp)).isPreconnected
  | S::T::rest,hc,hch => by
    have ih := chain_preconnected (T::rest) (fun U hU => hc U (List.mem_cons_of_mem _ hU))
      (List.isChain_cons_cons.mp hch).2
    have hS := (hc S (by simp)).isPreconnected
    obtain ⟨p,hpS,hpT⟩ := (List.isChain_cons_cons.mp hch).1
    have e : (⋃ U∈S::T::rest, U)=S∪⋃ U∈T::rest, U := by
      ext x; simp only [List.mem_cons,Set.mem_iUnion,Set.mem_union,exists_prop]
      constructor
      · rintro ⟨U,hU,hx⟩
        rcases hU with rfl|hU
        · exact Or.inl hx
        · exact Or.inr ⟨U,hU,hx⟩
      · rintro (hx|⟨U,hU,hx⟩)
        · exact ⟨S,Or.inl rfl,hx⟩
        · exact ⟨U,Or.inr hU,hx⟩
    rw [e]
    refine hS.union p hpS ?_ ih
    simp only [Set.mem_iUnion,exists_prop]
    exact ⟨T,List.mem_cons_self,hpT⟩

/-- A segment covered by a chain of closed convex sets with consecutive meeting points. -/
theorem segment_in_chain {g z : Point} (Rs : List (Set Point)) (hconv : ∀ R∈Rs, Convex ℝ R)
    (h0 : ∀ R, Rs.head?=some R → g∈R) (h1 : ∀ R, Rs.getLast?=some R → z∈R)
    (meet : Rs.IsChain (fun R R' => ∃ t : ℝ, 0≤t ∧ t≤1 ∧ Geometry.lerp g z t∈R∩R'))
    (ne : Rs≠[]) : ArtGallery.segment g z⊆⋃ R∈Rs, R := by
  let I : Set Point → Set ℝ := fun R => {t | 0≤t ∧ t≤1 ∧ Geometry.lerp g z t∈R}
  have Iconv (R : Set Point) (hR : Convex ℝ R) : Convex ℝ (I R) := by
    intro a ha b hb u v hu hv huv
    obtain ⟨a0,a1,ar⟩ := ha
    obtain ⟨b0,b1,br⟩ := hb
    refine ⟨by simp only [smul_eq_mul]; nlinarith,by simp only [smul_eq_mul]; nlinarith,?_⟩
    have e : Geometry.lerp g z (u•a+v•b)=u•Geometry.lerp g z a+v•Geometry.lerp g z b := by
      simp only [Geometry.lerp,smul_eq_mul]
      ext
      · simp only [Prod.fst_add,Prod.smul_fst,smul_eq_mul]; linear_combination (-g.1)*huv
      · simp only [Prod.snd_add,Prod.smul_snd,smul_eq_mul]; linear_combination (-g.2)*huv
    rw [e]; exact hR ar br hu hv huv
  have pre := chain_preconnected (Rs.map I) (by
      intro S hS; obtain ⟨R,hR,rfl⟩ := List.mem_map.mp hS; exact Iconv R (hconv R hR))
    (by
      rw [List.isChain_map]
      refine meet.imp ?_
      rintro R R' ⟨t,t0,t1,hR,hR'⟩
      exact ⟨t,⟨t0,t1,hR⟩,⟨t0,t1,hR'⟩⟩)
  have m0 : (0:ℝ)∈⋃ S∈Rs.map I, S := by
    obtain ⟨R,hR⟩ : ∃ R, Rs.head?=some R := by
      cases Rs with
      | nil => exact absurd rfl ne
      | cons R _ => exact ⟨R,rfl⟩
    simp only [Set.mem_iUnion,exists_prop]
    refine ⟨I R,List.mem_map.mpr ⟨R,List.mem_of_mem_head? hR,rfl⟩,le_rfl,zero_le_one,?_⟩
    simpa [Geometry.lerp] using h0 R hR
  have m1 : (1:ℝ)∈⋃ S∈Rs.map I, S := by
    obtain ⟨R,hR⟩ : ∃ R, Rs.getLast?=some R := ⟨Rs.getLast ne,List.getLast?_eq_getLast ne⟩
    simp only [Set.mem_iUnion,exists_prop]
    refine ⟨I R,List.mem_map.mpr ⟨R,List.mem_of_getLast? hR,rfl⟩,zero_le_one,le_rfl,?_⟩
    simpa [Geometry.lerp] using h1 R hR
  have cover := pre.Icc_subset m0 m1
  rintro p ⟨t,t0,t1,rfl⟩
  obtain ⟨S,hS,ht⟩ := Set.mem_iUnion₂.mp (cover ⟨t0,t1⟩)
  obtain ⟨R,hR,rfl⟩ := List.mem_map.mp hS
  exact Set.mem_iUnion₂.mpr ⟨R,hR,by simpa [Geometry.lerp] using ht.2.2⟩

/-! ## Bilinear sign extension -/

theorem det_lerp_first (a b z w : Point) (t : ℝ) :
    ArtGallery.det (Geometry.lerp a b t) z w=(1-t)*ArtGallery.det a z w+t*ArtGallery.det b z w := by
  simp only [ArtGallery.det,Geometry.lerp]; ring

theorem det_rect_second (g w : Point) (x₀ x₁ y₀ y₁ μ ν : ℝ) :
    ArtGallery.det g (x₀+μ*(x₁-x₀),y₀+ν*(y₁-y₀)) w=
      (1-μ)*(1-ν)*ArtGallery.det g (x₀,y₀) w+μ*(1-ν)*ArtGallery.det g (x₁,y₀) w+
      (1-μ)*ν*ArtGallery.det g (x₀,y₁) w+μ*ν*ArtGallery.det g (x₁,y₁) w := by
  simp only [ArtGallery.det]; ring

/-- A determinant nonnegative at the corners of a guard segment and a closed rectangle is
nonnegative on both. -/
theorem nonneg_on (σ : ℝ) {g₀ g₁ w : Point} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀≤x₁) (hy : y₀≤y₁)
    (h : ∀ g∈[g₀,g₁], ∀ z∈[((x₀,y₀):Point),(x₁,y₀),(x₀,y₁),(x₁,y₁)], 0≤σ*ArtGallery.det g z w)
    {g z : Point} (hg : g∈ArtGallery.segment g₀ g₁) (hz : z∈Rect x₀ x₁ y₀ y₁) : 0≤σ*ArtGallery.det g z w := by
  obtain ⟨t,t0,t1,hgt⟩ := Geometry.mem_segment_iff_lerp.mp hg
  obtain ⟨z0,z1,z2,z3⟩ := hz
  -- the target as a combination of the corners
  open Classical in
  let μ : ℝ := if x₀<x₁ then (z.1-x₀)/(x₁-x₀) else 0
  open Classical in
  let ν : ℝ := if y₀<y₁ then (z.2-y₀)/(y₁-y₀) else 0
  have hμ : 0≤μ ∧ μ≤1 ∧ z.1=x₀+μ*(x₁-x₀) := by
    simp only [μ]; split
    · next lt => exact ⟨div_nonneg (by linarith) (by linarith),(div_le_one (by linarith)).mpr (by linarith),
        by rw [div_mul_cancel₀ _ (by linarith : x₁-x₀≠0)]; ring⟩
    · next nlt => exact ⟨le_rfl,zero_le_one,by linarith [le_antisymm hx (not_lt.mp nlt)]⟩
  have hν : 0≤ν ∧ ν≤1 ∧ z.2=y₀+ν*(y₁-y₀) := by
    simp only [ν]; split
    · next lt => exact ⟨div_nonneg (by linarith) (by linarith),(div_le_one (by linarith)).mpr (by linarith),
        by rw [div_mul_cancel₀ _ (by linarith : y₁-y₀≠0)]; ring⟩
    · next nlt => exact ⟨le_rfl,zero_le_one,by linarith [le_antisymm hy (not_lt.mp nlt)]⟩
  obtain ⟨m0,m1,em⟩ := hμ
  obtain ⟨n0,n1,en⟩ := hν
  have ez : z=(x₀+μ*(x₁-x₀),y₀+ν*(y₁-y₀)) := by ext <;> simp only <;> assumption
  have at_end (g' : Point) (hg' : g'∈[g₀,g₁]) : 0≤σ*ArtGallery.det g' z w := by
    rw [ez,det_rect_second]
    rw [show σ*((1-μ)*(1-ν)*ArtGallery.det g' (x₀,y₀) w+μ*(1-ν)*ArtGallery.det g' (x₁,y₀) w+
      (1-μ)*ν*ArtGallery.det g' (x₀,y₁) w+μ*ν*ArtGallery.det g' (x₁,y₁) w)=
      (1-μ)*(1-ν)*(σ*ArtGallery.det g' (x₀,y₀) w)+μ*(1-ν)*(σ*ArtGallery.det g' (x₁,y₀) w)+
      (1-μ)*ν*(σ*ArtGallery.det g' (x₀,y₁) w)+μ*ν*(σ*ArtGallery.det g' (x₁,y₁) w) by ring]
    have h00 := h g' hg' (x₀,y₀) (by simp); have h10 := h g' hg' (x₁,y₀) (by simp)
    have h01 := h g' hg' (x₀,y₁) (by simp); have h11 := h g' hg' (x₁,y₁) (by simp)
    have w00 := mul_nonneg (mul_nonneg (sub_nonneg.2 m1) (sub_nonneg.2 n1)) h00
    have w10 := mul_nonneg (mul_nonneg m0 (sub_nonneg.2 n1)) h10
    have w01 := mul_nonneg (mul_nonneg (sub_nonneg.2 m1) n0) h01
    have w11 := mul_nonneg (mul_nonneg m0 n0) h11
    linarith
  rw [hgt,det_lerp_first]
  have a := at_end g₀ (by simp)
  have b := at_end g₁ (by simp)
  rw [show σ*((1-t)*ArtGallery.det g₀ z w+t*ArtGallery.det g₁ z w)=(1-t)*(σ*ArtGallery.det g₀ z w)+
    t*(σ*ArtGallery.det g₁ z w) by ring]
  exact add_nonneg (mul_nonneg (sub_nonneg.2 t1) a) (mul_nonneg t0 b)

/-- A sightline crosses a vertical window `x = c` between its window ends `(c,lo)`, `(c,hi)`. -/
theorem cross_vertical {g z : Point} {c lo hi : ℝ} (hgz : g.1<z.1) (hg : g.1≤c) (hz : c≤z.1)
    (slo : ArtGallery.det g z (c,lo)≤0) (shi : 0≤ArtGallery.det g z (c,hi)) :
    ∃ t : ℝ, 0≤t ∧ t≤1 ∧ (Geometry.lerp g z t).1=c ∧ lo≤(Geometry.lerp g z t).2 ∧ (Geometry.lerp g z t).2≤hi := by
  have d : 0<z.1-g.1 := sub_pos.2 hgz
  set t := (c-g.1)/(z.1-g.1) with ht
  have et : t*(z.1-g.1)=c-g.1 := by rw [ht,div_mul_cancel₀ _ d.ne']
  have k (y : ℝ) : (z.1-g.1)*((Geometry.lerp g z t).2-y)=-ArtGallery.det g z (c,y) := by
    simp only [Geometry.lerp,ArtGallery.det]; linear_combination (z.2-g.2)*et
  refine ⟨t,div_nonneg (by linarith) d.le,(div_le_one d).mpr (by linarith),?_,?_,?_⟩
  · simp only [Geometry.lerp]; linarith
  · have := k lo; exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left d).mp (by rw [this]; linarith))
  · have := k hi
    have h2 : (z.1-g.1)*((Geometry.lerp g z t).2-hi)≤0 := by rw [this]; linarith
    have := nonpos_of_mul_nonpos_right (by linarith : (z.1-g.1)*((Geometry.lerp g z t).2-hi)≤0) d
    linarith

/-- A sightline crosses a horizontal window `y = c` between its window ends `(lo,c)`, `(hi,c)`. -/
theorem cross_horizontal {g z : Point} {c lo hi : ℝ} (hgz : g.2<z.2) (hg : g.2≤c) (hz : c≤z.2)
    (slo : 0≤ArtGallery.det g z (lo,c)) (shi : ArtGallery.det g z (hi,c)≤0) :
    ∃ t : ℝ, 0≤t ∧ t≤1 ∧ (Geometry.lerp g z t).2=c ∧ lo≤(Geometry.lerp g z t).1 ∧ (Geometry.lerp g z t).1≤hi := by
  have d : 0<z.2-g.2 := sub_pos.2 hgz
  set t := (c-g.2)/(z.2-g.2) with ht
  have et : t*(z.2-g.2)=c-g.2 := by rw [ht,div_mul_cancel₀ _ d.ne']
  have k (x : ℝ) : (z.2-g.2)*((Geometry.lerp g z t).1-x)=ArtGallery.det g z (x,c) := by
    simp only [Geometry.lerp,ArtGallery.det]; linear_combination (z.1-g.1)*et
  refine ⟨t,div_nonneg (by linarith) d.le,(div_le_one d).mpr (by linarith),?_,?_,?_⟩
  · simp only [Geometry.lerp]; linarith
  · have := k lo; exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left d).mp (by rw [this]; exact slo))
  · have := k hi
    have := nonpos_of_mul_nonpos_right (by rw [this]; exact shi : (z.2-g.2)*((Geometry.lerp g z t).1-hi)≤0) d
    linarith

theorem lerp_symm (g z : Point) (t : ℝ) : Geometry.lerp z g t=Geometry.lerp g z (1-t) := by
  simp only [Geometry.lerp]; ext <;> simp only <;> ring

theorem det_swap (g z w : Point) : ArtGallery.det z g w= -ArtGallery.det g z w := by
  simp only [ArtGallery.det]; ring

theorem det_cycle (g z w : Point) : ArtGallery.det g z w=ArtGallery.det w g z := by
  simp only [ArtGallery.det]; ring

/-! ## Certificates -/

/-- A window on a grid line: vertical (`x = X[c]`) or horizontal (`y = Y[c]`), between the line
indices `lo ≤ hi`; `dir` says the guard lies on the side of smaller coordinates. -/
structure Win where
  vert : Bool
  dir : Bool
  c : Nat
  lo : Nat
  hi : Nat

/-- Certificate of a guard segment and a cell: tile indices and windows with sixteen signs
(guard end × cell corner × window end). -/
structure Cert where
  ts : List Nat
  ws : List (Win × List Sign)

def tileOf (C : Chart) (i : Nat) : CorridorProgram.Rect Nat := C.tiles.getD i (0,0,0,0)

def inRect (r : CorridorProgram.Rect Nat) (p : Index) : Bool :=
  decide (r.1≤p.1 ∧ p.1≤r.2.1 ∧ r.2.2.1≤p.2 ∧ p.2≤r.2.2.2)

def cellIn (r : CorridorProgram.Rect Nat) (x x' y y' : Nat) : Bool :=
  decide (r.1≤x ∧ x'≤r.2.1 ∧ r.2.2.1≤y ∧ y'≤r.2.2.2)

def cornersOf (x x' y y' : Nat) : List Index := [(x,y),(x',y),(x,y'),(x',y')]

/-- The window's two end nodes. -/
def Win.lo' (w : Win) : Index := if w.vert then (w.c,w.lo) else (w.lo,w.c)
def Win.hi' (w : Win) : Index := if w.vert then (w.c,w.hi) else (w.hi,w.c)

/-- Signs wanted at the window ends: `det(g,z,lo') ≤ 0 ≤ det(g,z,hi')` for a vertical window crossed
rightwards, reversed for the other direction and for horizontal windows. -/
def Win.posLo (w : Win) : Bool := w.vert != w.dir

def Win.place (w : Win) (a b : CorridorProgram.Rect Nat) : Bool :=
  if w.vert then decide (a.1≤w.c ∧ w.c≤a.2.1 ∧ b.1≤w.c ∧ w.c≤b.2.1 ∧ a.2.2.1≤w.lo ∧ b.2.2.1≤w.lo ∧
    w.lo≤w.hi ∧ w.hi≤a.2.2.2 ∧ w.hi≤b.2.2.2)
  else decide (a.2.2.1≤w.c ∧ w.c≤a.2.2.2 ∧ b.2.2.1≤w.c ∧ w.c≤b.2.2.2 ∧ a.1≤w.lo ∧ b.1≤w.lo ∧
    w.lo≤w.hi ∧ w.hi≤a.2.1 ∧ w.hi≤b.2.1)

/-- The window line separates the guard ends from the cell, strictly on one side. -/
def Win.sep (w : Win) (g₀ g₁ : Index) (x x' y y' : Nat) : Bool :=
  let u₀ := if w.vert then g₀.1 else g₀.2
  let u₁ := if w.vert then g₁.1 else g₁.2
  let v := if w.vert then x else y
  let v' := if w.vert then x' else y'
  if w.dir then decide (u₀≤w.c ∧ u₁≤w.c ∧ w.c≤v ∧ ((u₀<w.c ∧ u₁<w.c) ∨ w.c<v))
  else decide (v'≤w.c ∧ w.c≤u₀ ∧ w.c≤u₁ ∧ (v'<w.c ∨ (w.c<u₀ ∧ w.c<u₁)))

def Win.signs (C : Chart) (w : Win) (g₀ g₁ : Index) (x x' y y' : Nat) (ss : List Sign) : Bool :=
  let pairs := ([g₀,g₁].flatMap fun g => (cornersOf x x' y y').map fun z => (g,z))
  decide (ss.length=16) &&
  (List.range 8).all fun i =>
    let p := pairs.getD i ((0,0),(0,0))
    C.detSign w.posLo w.lo' p.1 p.2 (ss.getD (2*i) .zero) &&
    C.detSign (!w.posLo) w.hi' p.1 p.2 (ss.getD (2*i+1) .zero)

def chainOK (C : Chart) (g₀ g₁ : Index) (x x' y y' : Nat) : List Nat → List (Win × List Sign) → Bool
  | [t],[] => cellIn (tileOf C t) x x' y y'
  | t::u::rest,(w,ss)::ws => w.place (tileOf C t) (tileOf C u) && w.sep g₀ g₁ x x' y y' &&
      w.signs C g₀ g₁ x x' y y' ss && chainOK C g₀ g₁ x x' y y' (u::rest) ws
  | _,_ => false

def Cert.ok (C : Chart) (g₀ g₁ : Index) (x x' y y' : Nat) (c : Cert) : Bool :=
  match c.ts with
  | [] => false
  | t::_ => inRect (tileOf C t) g₀ && inRect (tileOf C t) g₁ && chainOK C g₀ g₁ x x' y y' c.ts c.ws &&
      c.ts.all (· < C.tiles.length) && decide (g₀.1<C.nx ∧ g₀.2<C.ny ∧ g₁.1<C.nx ∧ g₁.2<C.ny ∧ x<x' ∧ x'<C.nx ∧ y<y' ∧ y'<C.ny)

/-! ## Soundness -/

section Sound
variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

theorem lev_le {X : List ℝ} (hx : X.IsChain (·<·)) {i j : Nat} (hj : j<X.length) (h : i≤j) :
    X.getD i 0≤X.getD j 0 := by
  rcases eq_or_lt_of_le h with rfl|lt
  · exact le_rfl
  · exact (SepGeom.level_lt hx hj lt).le

def realRect (X Y : List ℝ) (r : CorridorProgram.Rect Nat) : Set Point :=
  Rect (X.getD r.1 0) (X.getD r.2.1 0) (Y.getD r.2.2.1 0) (Y.getD r.2.2.2 0)

theorem tile_sub (G : Good C X Y s A) {i : Nat} (hi : i<C.tiles.length) :
    realRect X Y (tileOf C i)⊆(C.poly X Y).filled := by
  intro p hp
  rw [G.fill]
  have e : tileOf C i=C.tiles[i] := by unfold tileOf; rw [List.getD_eq_getElem _ _ hi]
  rw [e] at hp
  exact ⟨C.tiles[i],List.getElem_mem hi,hp⟩

theorem tile_idx (G : Good C X Y s A) {i : Nat} (hi : i<C.tiles.length) :
    (tileOf C i).1<X.length ∧ (tileOf C i).2.1<X.length ∧ (tileOf C i).2.2.1<Y.length ∧ (tileOf C i).2.2.2<Y.length := by
  have e : tileOf C i=C.tiles[i] := by unfold tileOf; rw [List.getD_eq_getElem _ _ hi]
  rw [e,G.lx,G.ly]; exact G.tileIdx _ (List.getElem_mem hi)

theorem node_in (G : Good C X Y s A) {r : CorridorProgram.Rect Nat}
    (hr : r.1<X.length ∧ r.2.1<X.length ∧ r.2.2.1<Y.length ∧ r.2.2.2<Y.length) {p : Index}
    (hp : inRect r p=true) : gridPt X Y p∈realRect X Y r := by
  simp only [inRect,decide_eq_true_eq] at hp
  obtain ⟨a,b,c,d⟩ := hp
  exact ⟨lev_le G.hx (by omega) a,lev_le G.hx hr.2.1 b,lev_le G.hy (by omega) c,lev_le G.hy hr.2.2.2 d⟩

theorem sign_fact (G : Good C X Y s A) {pos : Bool} {w g z : Index} {sg : Sign}
    (hw : w.1<C.nx ∧ w.2<C.ny) (hg : g.1<C.nx ∧ g.2<C.ny) (hz : z.1<C.nx ∧ z.2<C.ny)
    (h : C.detSign pos w g z sg=true) :
    0≤(if pos then 1 else -1)*ArtGallery.det (gridPt X Y g) (gridPt X Y z) (gridPt X Y w) := by
  have f := detSign_sound G hw hg hz h
  rw [det_cycle (gridPt X Y g)]
  cases hz' : sg.isZero
  · have := f.2 hz'
    cases pos
    · simp only [Bool.false_eq_true,ite_false]; linarith [this.2 rfl]
    · simp only [ite_true]; linarith [this.1 rfl]
  · rw [f.1 hz']; simp

theorem seg_coord {p q g : Point} (hg : g∈ArtGallery.segment p q) (f : Point → ℝ)
    (hf : ∀ t : ℝ, f (Geometry.lerp p q t)=(1-t)*f p+t*f q) {v : ℝ} :
    (f p≤v → f q≤v → f g≤v) ∧ (f p<v → f q<v → f g<v) ∧ (v≤f p → v≤f q → v≤f g) ∧ (v<f p → v<f q → v<f g) := by
  obtain ⟨t,t0,t1,rfl⟩ := Geometry.mem_segment_iff_lerp.mp hg
  rw [hf]
  have w0 := sub_nonneg.2 t1
  refine ⟨fun a b => ?_,fun a b => ?_,fun a b => ?_,fun a b => ?_⟩
  · nlinarith [mul_nonneg w0 (sub_nonneg.2 a),mul_nonneg t0 (sub_nonneg.2 b)]
  · rcases eq_or_lt_of_le t0 with e|e
    · subst e; simpa using a
    · nlinarith [mul_nonneg w0 (sub_nonneg.2 a.le),mul_pos e (sub_pos.2 b)]
  · nlinarith [mul_nonneg w0 (sub_nonneg.2 a),mul_nonneg t0 (sub_nonneg.2 b)]
  · rcases eq_or_lt_of_le t0 with e|e
    · subst e; simpa using a
    · nlinarith [mul_nonneg w0 (sub_nonneg.2 a.le),mul_pos e (sub_pos.2 b)]

theorem pairs_mem {g₀ g₁ : Index} {x x' y y' : Nat} {g z : Index} (hg : g∈[g₀,g₁]) (hz : z∈cornersOf x x' y y') :
    ∃ i, i<8 ∧ ([g₀,g₁].flatMap fun g => (cornersOf x x' y y').map fun z => (g,z)).getD i ((0,0),(0,0))=(g,z) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,cornersOf] at hg hz
  rcases hg with rfl|rfl <;> rcases hz with rfl|rfl|rfl|rfl
  exacts [⟨0,by norm_num,rfl⟩,⟨1,by norm_num,rfl⟩,⟨2,by norm_num,rfl⟩,⟨3,by norm_num,rfl⟩,
    ⟨4,by norm_num,rfl⟩,⟨5,by norm_num,rfl⟩,⟨6,by norm_num,rfl⟩,⟨7,by norm_num,rfl⟩]

/-- The meeting point of a sightline with a window line, on either side. -/
theorem meetV {g z : Point} {c lo hi : ℝ} (dir : Bool)
    (side : if dir then g.1≤c ∧ c≤z.1 ∧ g.1<z.1 else z.1≤c ∧ c≤g.1 ∧ z.1<g.1)
    (slo : 0≤(if dir then -1 else 1)*ArtGallery.det g z (c,lo))
    (shi : 0≤(if dir then 1 else -1)*ArtGallery.det g z (c,hi)) :
    ∃ t : ℝ, 0≤t ∧ t≤1 ∧ (Geometry.lerp g z t).1=c ∧ lo≤(Geometry.lerp g z t).2 ∧ (Geometry.lerp g z t).2≤hi := by
  cases dir
  · simp only [Bool.false_eq_true,ite_false] at side slo shi
    obtain ⟨t,t0,t1,e,l,h⟩ := cross_vertical (g:=z) (z:=g) (c:=c) (lo:=lo) (hi:=hi) side.2.2 side.1 side.2.1
      (by rw [det_swap]; linarith) (by rw [det_swap]; linarith)
    refine ⟨1-t,by linarith,by linarith,?_⟩
    rw [← lerp_symm]; exact ⟨e,l,h⟩
  · simp only [ite_true] at side slo shi
    exact cross_vertical (c:=c) (lo:=lo) (hi:=hi) side.2.2 side.1 side.2.1 (by linarith) (by linarith)

theorem meetH {g z : Point} {c lo hi : ℝ} (dir : Bool)
    (side : if dir then g.2≤c ∧ c≤z.2 ∧ g.2<z.2 else z.2≤c ∧ c≤g.2 ∧ z.2<g.2)
    (slo : 0≤(if dir then 1 else -1)*ArtGallery.det g z (lo,c))
    (shi : 0≤(if dir then -1 else 1)*ArtGallery.det g z (hi,c)) :
    ∃ t : ℝ, 0≤t ∧ t≤1 ∧ (Geometry.lerp g z t).2=c ∧ lo≤(Geometry.lerp g z t).1 ∧ (Geometry.lerp g z t).1≤hi := by
  cases dir
  · simp only [Bool.false_eq_true,ite_false] at side slo shi
    obtain ⟨t,t0,t1,e,l,h⟩ := cross_horizontal (g:=z) (z:=g) (c:=c) (lo:=lo) (hi:=hi) side.2.2 side.1 side.2.1
      (by rw [det_swap]; linarith) (by rw [det_swap]; linarith)
    refine ⟨1-t,by linarith,by linarith,?_⟩
    rw [← lerp_symm]; exact ⟨e,l,h⟩
  · simp only [ite_true] at side slo shi
    exact cross_horizontal (c:=c) (lo:=lo) (hi:=hi) side.2.2 side.1 side.2.1 (by linarith) (by linarith)

set_option maxHeartbeats 4000000 in
/-- Every sightline from the guard segment to the cell meets the window of two consecutive tiles. -/
theorem window_meet (G : Good C X Y s A) {g₀ g₁ : Index} {x x' y y' : Nat} {w : Win} {ss : List Sign}
    {a b : CorridorProgram.Rect Nat}
    (ha : a.1<X.length ∧ a.2.1<X.length ∧ a.2.2.1<Y.length ∧ a.2.2.2<Y.length)
    (hb : b.1<X.length ∧ b.2.1<X.length ∧ b.2.2.1<Y.length ∧ b.2.2.2<Y.length)
    (hp : w.place a b=true) (hs : w.sep g₀ g₁ x x' y y'=true) (hsg : w.signs C g₀ g₁ x x' y y' ss=true)
    (rg : g₀.1<C.nx ∧ g₀.2<C.ny ∧ g₁.1<C.nx ∧ g₁.2<C.ny ∧ x<x' ∧ x'<C.nx ∧ y<y' ∧ y'<C.ny)
    {g z : Point} (hg : g∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁))
    (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0)) :
    ∃ t : ℝ, 0≤t ∧ t≤1 ∧ Geometry.lerp g z t∈realRect X Y a∩realRect X Y b := by
  obtain ⟨r0x,r0y,r1x,r1y,rx,ry⟩ := rg
  have lx := G.lx; have ly := G.ly
  have hlo : w.lo'.1<C.nx ∧ w.lo'.2<C.ny := by
    rcases w with ⟨vert,dir,c,lo,hi⟩
    cases vert <;> simp only [Win.place,Win.lo',ite_true,ite_false,Bool.false_eq_true,decide_eq_true_eq] at hp ⊢ <;> omega
  have hhi : w.hi'.1<C.nx ∧ w.hi'.2<C.ny := by
    rcases w with ⟨vert,dir,c,lo,hi⟩
    cases vert <;> simp only [Win.place,Win.hi',ite_true,ite_false,Bool.false_eq_true,decide_eq_true_eq] at hp ⊢ <;> omega
  -- the signs at the eight pairs
  simp only [Win.signs,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range] at hsg
  obtain ⟨-,hall⟩ := hsg
  have cr (z' : Index) (hz' : z'∈cornersOf x x' y y') : z'.1<C.nx ∧ z'.2<C.ny := by
    simp only [cornersOf,List.mem_cons,List.not_mem_nil,or_false] at hz'
    rcases hz' with rfl|rfl|rfl|rfl <;> simp <;> omega
  have gr (g' : Index) (hg' : g'∈[g₀,g₁]) : g'.1<C.nx ∧ g'.2<C.ny := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hg'; rcases hg' with rfl|rfl <;> simp_all
  have signs (g' : Index) (hg' : g'∈[g₀,g₁]) (z' : Index) (hz' : z'∈cornersOf x x' y y') :
      0≤(if w.posLo then 1 else -1)*ArtGallery.det (gridPt X Y g') (gridPt X Y z') (gridPt X Y w.lo') ∧
      0≤(if !w.posLo then 1 else -1)*ArtGallery.det (gridPt X Y g') (gridPt X Y z') (gridPt X Y w.hi') := by
    obtain ⟨i,hi,e⟩ := pairs_mem hg' hz'
    have h := hall i hi
    rw [e] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨sign_fact G hlo (gr g' hg') (cr z' hz') h.1,sign_fact G hhi (gr g' hg') (cr z' hz') h.2⟩
  have cell : x'<X.length ∧ y'<Y.length := ⟨by omega,by omega⟩
  have hxx : X.getD x 0≤X.getD x' 0 := lev_le G.hx cell.1 (by omega)
  have hyy : Y.getD y 0≤Y.getD y' 0 := lev_le G.hy cell.2 (by omega)
  have ext (σ : ℝ) (v : Index) (h : ∀ g'∈[g₀,g₁], ∀ z'∈cornersOf x x' y y', 0≤σ*ArtGallery.det (gridPt X Y g') (gridPt X Y z') (gridPt X Y v)) :
      0≤σ*ArtGallery.det g z (gridPt X Y v) := by
    apply nonneg_on σ hxx hyy _ hg hz
    intro g' hg' z' hz'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hg' hz'
    have m0 : g₀∈[g₀,g₁] := List.mem_cons_self
    have m1 : g₁∈[g₀,g₁] := List.mem_cons_of_mem _ List.mem_cons_self
    have c00 : ((x,y):Index)∈cornersOf x x' y y' := List.mem_cons_self
    have c10 : ((x',y):Index)∈cornersOf x x' y y' := by simp [cornersOf]
    have c01 : ((x,y'):Index)∈cornersOf x x' y y' := by simp [cornersOf]
    have c11 : ((x',y'):Index)∈cornersOf x x' y y' := by simp [cornersOf]
    rcases hg' with rfl|rfl <;> rcases hz' with rfl|rfl|rfl|rfl
    · exact h g₀ m0 _ c00
    · exact h g₀ m0 _ c10
    · exact h g₀ m0 _ c01
    · exact h g₀ m0 _ c11
    · exact h g₁ m1 _ c00
    · exact h g₁ m1 _ c10
    · exact h g₁ m1 _ c01
    · exact h g₁ m1 _ c11
  have sLo := ext _ w.lo' (fun g' hg' z' hz' => (signs g' hg' z' hz').1)
  have sHi := ext _ w.hi' (fun g' hg' z' hz' => (signs g' hg' z' hz').2)
  obtain ⟨z0,z1,z2,z3⟩ := hz
  have c1 (v : ℝ) := seg_coord hg Prod.fst (fun t => by simp [Geometry.lerp]; ring) (v:=v)
  have c2 (v : ℝ) := seg_coord hg Prod.snd (fun t => by simp [Geometry.lerp]; ring) (v:=v)
  simp only [gridPt] at c1 c2
  have lvx {i j : Nat} (hj : j<C.nx) (h : i≤j) := lev_le G.hx (by omega : j<X.length) h
  have lvy {i j : Nat} (hj : j<C.ny) (h : i≤j) := lev_le G.hy (by omega : j<Y.length) h
  have ltx {i j : Nat} (hj : j<C.nx) (h : i<j) := SepGeom.level_lt G.hx (by omega : j<X.length) h
  have lty {i j : Nat} (hj : j<C.ny) (h : i<j) := SepGeom.level_lt G.hy (by omega : j<Y.length) h
  have ax2 : a.2.1<C.nx := by rw [← lx]; exact ha.2.1
  have ay2 : a.2.2.2<C.ny := by rw [← ly]; exact ha.2.2.2
  have bx2 : b.2.1<C.nx := by rw [← lx]; exact hb.2.1
  have by2 : b.2.2.2<C.ny := by rw [← ly]; exact hb.2.2.2
  rcases w with ⟨vert,dir,c,lo,hi⟩
  cases vert <;> cases dir <;>
    simp only [Win.place,Win.sep,Win.posLo,Win.lo',Win.hi',gridPt,ite_true,ite_false,Bool.false_eq_true,
      decide_eq_true_eq,bne_self_eq_false,Bool.true_bne,Bool.false_bne,Bool.not_true,Bool.not_false] at hp hs sLo sHi
  · -- horizontal, guard above
    obtain ⟨p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := hp
    obtain ⟨v1,u0,u1,str⟩ := hs
    have hcy : c<C.ny := by omega
    have e0 := lvy r0y u0; have e1 := lvy r1y u1; have e2 := lvy hcy v1
    have gc := (c2 (Y.getD c 0)).2.2.1 e0 e1
    have strict : z.2<g.2 := by
      rcases str with st|⟨s0,s1⟩
      · have := lty hcy st; linarith
      · have := (c2 (Y.getD c 0)).2.2.2 (lty r0y s0) (lty r1y s1); linarith
    obtain ⟨t,t0,t1,ey,elo,ehi⟩ := meetH (g:=g) (z:=z) (c:=Y.getD c 0) (lo:=X.getD lo 0) (hi:=X.getD hi 0) false
      (by simp only [Bool.false_eq_true,ite_false]; exact ⟨by linarith,gc,strict⟩)
      (by simp only [Bool.false_eq_true,ite_false]; linarith) (by simp only [Bool.false_eq_true,ite_false]; linarith)
    refine ⟨t,t0,t1,⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩
    · have := lvx (by omega) p5; linarith
    · have := lvx ax2 p8; linarith
    · rw [ey]; exact lvy hcy p1
    · rw [ey]; exact lvy ay2 p2
    · have := lvx (by omega) p6; linarith
    · have := lvx bx2 p9; linarith
    · rw [ey]; exact lvy hcy p3
    · rw [ey]; exact lvy by2 p4
  · -- horizontal, guard below
    obtain ⟨p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := hp
    obtain ⟨u0,u1,v1,str⟩ := hs
    have hcy : c<C.ny := by omega
    have e0 := lvy hcy u0; have e1 := lvy hcy u1; have e2 := lvy (by omega) v1
    have gc := (c2 (Y.getD c 0)).1 e0 e1
    have strict : g.2<z.2 := by
      rcases str with ⟨s0,s1⟩|st
      · have := (c2 (Y.getD c 0)).2.1 (lty hcy s0) (lty hcy s1); linarith
      · have := lty (by omega) st; linarith
    obtain ⟨t,t0,t1,ey,elo,ehi⟩ := meetH (g:=g) (z:=z) (c:=Y.getD c 0) (lo:=X.getD lo 0) (hi:=X.getD hi 0) true
      (by simp only [ite_true]; exact ⟨gc,by linarith,strict⟩)
      (by simp only [ite_true]; linarith) (by simp only [ite_true]; linarith)
    refine ⟨t,t0,t1,⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩
    · have := lvx (by omega) p5; linarith
    · have := lvx ax2 p8; linarith
    · rw [ey]; exact lvy hcy p1
    · rw [ey]; exact lvy ay2 p2
    · have := lvx (by omega) p6; linarith
    · have := lvx bx2 p9; linarith
    · rw [ey]; exact lvy hcy p3
    · rw [ey]; exact lvy by2 p4
  · -- vertical, guard right
    obtain ⟨p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := hp
    obtain ⟨v1,u0,u1,str⟩ := hs
    have hcx : c<C.nx := by omega
    have e0 := lvx r0x u0; have e1 := lvx r1x u1; have e2 := lvx hcx v1
    have gc := (c1 (X.getD c 0)).2.2.1 e0 e1
    have strict : z.1<g.1 := by
      rcases str with st|⟨s0,s1⟩
      · have := ltx hcx st; linarith
      · have := (c1 (X.getD c 0)).2.2.2 (ltx r0x s0) (ltx r1x s1); linarith
    obtain ⟨t,t0,t1,ex,elo,ehi⟩ := meetV (g:=g) (z:=z) (c:=X.getD c 0) (lo:=Y.getD lo 0) (hi:=Y.getD hi 0) false
      (by simp only [Bool.false_eq_true,ite_false]; exact ⟨by linarith,gc,strict⟩)
      (by simp only [Bool.false_eq_true,ite_false]; linarith) (by simp only [Bool.false_eq_true,ite_false]; linarith)
    refine ⟨t,t0,t1,⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩
    · rw [ex]; exact lvx hcx p1
    · rw [ex]; exact lvx ax2 p2
    · have := lvy (by omega) p5; linarith
    · have := lvy ay2 p8; linarith
    · rw [ex]; exact lvx hcx p3
    · rw [ex]; exact lvx bx2 p4
    · have := lvy (by omega) p6; linarith
    · have := lvy by2 p9; linarith
  · -- vertical, guard left
    obtain ⟨p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := hp
    obtain ⟨u0,u1,v1,str⟩ := hs
    have hcx : c<C.nx := by omega
    have e0 := lvx hcx u0; have e1 := lvx hcx u1; have e2 := lvx (by omega) v1
    have gc := (c1 (X.getD c 0)).1 e0 e1
    have strict : g.1<z.1 := by
      rcases str with ⟨s0,s1⟩|st
      · have := (c1 (X.getD c 0)).2.1 (ltx hcx s0) (ltx hcx s1); linarith
      · have := ltx (by omega) st; linarith
    obtain ⟨t,t0,t1,ex,elo,ehi⟩ := meetV (g:=g) (z:=z) (c:=X.getD c 0) (lo:=Y.getD lo 0) (hi:=Y.getD hi 0) true
      (by simp only [ite_true]; exact ⟨gc,by linarith,strict⟩)
      (by simp only [ite_true]; linarith) (by simp only [ite_true]; linarith)
    refine ⟨t,t0,t1,⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩
    · rw [ex]; exact lvx hcx p1
    · rw [ex]; exact lvx ax2 p2
    · have := lvy (by omega) p5; linarith
    · have := lvy ay2 p8; linarith
    · rw [ex]; exact lvx hcx p3
    · rw [ex]; exact lvx bx2 p4
    · have := lvy (by omega) p6; linarith
    · have := lvy by2 p9; linarith

theorem chain_facts (G : Good C X Y s A) {g₀ g₁ : Index} {x x' y y' : Nat}
    (rg : g₀.1<C.nx ∧ g₀.2<C.ny ∧ g₁.1<C.nx ∧ g₁.2<C.ny ∧ x<x' ∧ x'<C.nx ∧ y<y' ∧ y'<C.ny)
    {g z : Point} (hg : g∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁))
    (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0)) :
    ∀ (ts : List Nat) (ws : List (Win × List Sign)), chainOK C g₀ g₁ x x' y y' ts ws=true →
      (∀ i∈ts, i<C.tiles.length) →
      (∀ R, (ts.map (fun i => realRect X Y (tileOf C i))).getLast?=some R → z∈R) ∧
      (ts.map (fun i => realRect X Y (tileOf C i))).IsChain
        (fun R R' => ∃ t : ℝ, 0≤t ∧ t≤1 ∧ Geometry.lerp g z t∈R∩R')
  | [],_,h,_ => by simp [chainOK] at h
  | [t],[],h,hi => by
    have ti := tile_idx G (hi t (by simp))
    simp only [chainOK,cellIn,decide_eq_true_eq] at h
    obtain ⟨a0,a1,a2,a3⟩ := h
    obtain ⟨z0,z1,z2,z3⟩ := hz
    refine ⟨fun R hR => ?_,List.isChain_singleton _⟩
    simp only [List.map_cons,List.map_nil,List.getLast?_singleton,Option.some.injEq] at hR
    subst hR
    have lx := G.lx; have ly := G.ly
    refine ⟨?_,?_,?_,?_⟩
    · exact (lev_le G.hx (by omega) a0).trans z0
    · exact z1.trans (lev_le G.hx ti.2.1 a1)
    · exact (lev_le G.hy (by omega) a2).trans z2
    · exact z3.trans (lev_le G.hy ti.2.2.2 a3)
  | [_],_::_,h,_ => by simp [chainOK] at h
  | _::_::_,[],h,_ => by simp [chainOK] at h
  | t::u::rest,(w,ss)::ws,h,hi => by
    simp only [chainOK,Bool.and_eq_true] at h
    obtain ⟨⟨⟨hp,hs⟩,hsg⟩,hrest⟩ := h
    have ih := chain_facts G rg hg hz (u::rest) ws hrest (fun i hi' => hi i (List.mem_cons_of_mem _ hi'))
    have m := window_meet G (tile_idx G (hi t (by simp))) (tile_idx G (hi u (by simp))) hp hs hsg rg hg hz
    refine ⟨fun R hR => ih.1 R (by simpa using hR),?_⟩
    simp only [List.map_cons] at ih ⊢
    exact List.isChain_cons_cons.mpr ⟨m,ih.2⟩

/-- Soundness of a chain certificate: every point of the guard segment sees every point of the
closed cell. -/
theorem Cert.sound (G : Good C X Y s A) {g₀ g₁ : Index} {x x' y y' : Nat} {c : Cert} (h : c.ok C g₀ g₁ x x' y y'=true)
    {g z : Point} (hg : g∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁))
    (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0)) : (C.poly X Y).Sees g z := by
  unfold Cert.ok at h
  split at h
  · simp at h
  · next t rest hts =>
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
    obtain ⟨⟨⟨⟨i0,i1⟩,hch⟩,hidx⟩,rg⟩ := h
    have hidx' : ∀ i∈c.ts, i<C.tiles.length := fun i hi => by simpa using hidx i hi
    have ti := tile_idx G (hidx' t (by rw [hts]; simp))
    have g0 := node_in G ti i0
    have g1 := node_in G ti i1
    have gR : g∈realRect X Y (tileOf C t) := by
      obtain ⟨u,u0,u1,rfl⟩ := Geometry.mem_segment_iff_lerp.mp hg
      exact lerp_rect g0 g1 u0 u1
    have facts := chain_facts G rg hg hz c.ts c.ws hch hidx'
    have sub := segment_in_chain (c.ts.map (fun i => realRect X Y (tileOf C i)))
      (fun R hR => by obtain ⟨i,-,rfl⟩ := List.mem_map.mp hR; exact rect_convex _ _ _ _)
      (fun R hR => by rw [hts] at hR; simp only [List.map_cons,List.head?_cons,Option.some.injEq] at hR; rw [← hR]; exact gR)
      facts.1 facts.2 (by rw [hts]; simp)
    intro p hp
    obtain ⟨R,hR,hpR⟩ := Set.mem_iUnion₂.mp (sub hp)
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hR
    exact tile_sub G (hidx' i hi) hpR

end Sound

/-! ## Covering a chart by certified rectangles -/

section Cover
variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

/-- A coordinate between two grid lines lies in one closed cell between them. -/
theorem cell_exists {X : List ℝ} (hx : X.IsChain (·<·)) {v : ℝ} :
    ∀ (k a : Nat), a+k<X.length → 0<k → X.getD a 0≤v → v≤X.getD (a+k) 0 →
      ∃ i, a ≤ i ∧ i<a+k ∧ X.getD i 0≤v ∧ v≤X.getD (i+1) 0
  | 0,_,_,h,_,_ => absurd h (lt_irrefl 0)
  | k+1,a,hb,_,h0,h1 => by
    by_cases hv : v≤X.getD (a+1) 0
    · exact ⟨a,le_rfl,by omega,h0,hv⟩
    · have hk : 0<k := by
        rcases Nat.eq_zero_or_pos k with e|e
        · subst e; exact absurd h1 hv
        · exact e
      obtain ⟨i,i0,i1,i2,i3⟩ := cell_exists hx k (a+1) (by omega) hk (le_of_lt (not_le.mp hv))
        (by rw [show a+1+k=a+(k+1) by omega]; exact h1)
      exact ⟨i,by omega,by omega,i2,i3⟩

theorem point_cell (G : Good C X Y s A) (hnd : ∀ t∈C.tiles, t.1<t.2.1 ∧ t.2.2.1<t.2.2.2)
    {z : Point} (hz : z∈(C.poly X Y).filled) :
    ∃ t∈C.tiles, ∃ i j, t.1 ≤ i ∧ i<t.2.1 ∧ t.2.2.1≤j ∧ j<t.2.2.2 ∧
      z∈Rect (X.getD i 0) (X.getD (i+1) 0) (Y.getD j 0) (Y.getD (j+1) 0) := by
  rw [G.fill] at hz
  obtain ⟨t,ht,a,b,c,d⟩ := hz
  have idx := G.tileIdx t ht
  have lx := G.lx; have ly := G.ly
  obtain ⟨nx,ny⟩ := hnd t ht
  obtain ⟨i,i0,i1,i2,i3⟩ := cell_exists G.hx (t.2.1-t.1) t.1 (by omega) (by omega) a
    (by rw [show t.1+(t.2.1-t.1)=t.2.1 by omega]; exact b)
  obtain ⟨j,j0,j1,j2,j3⟩ := cell_exists G.hy (t.2.2.2-t.2.2.1) t.2.2.1 (by omega) (by omega) c
    (by rw [show t.2.2.1+(t.2.2.2-t.2.2.1)=t.2.2.2 by omega]; exact d)
  exact ⟨t,ht,i,j,i0,by omega,j0,by omega,i2,i3,j2,j3⟩

/-- A certified rectangle of cells `[x,x']×[y,y']`, seen from the canonical point of a role
(`point`) or from its whole spot. -/
structure Entry where
  x : Nat
  x' : Nat
  y : Nat
  y' : Nat
  role : Nat
  point : Bool
  cert : Cert

def Entry.ends (roles : List (List Index)) (e : Entry) : Index × Index :=
  let l := roles.getD e.role []
  if e.point then (l.getD 0 (0,0),l.getD 0 (0,0)) else (CellRoles.spotA l,CellRoles.spotB l)

def Entry.good (C : Chart) (roles : List (List Index)) (e : Entry) : Bool :=
  decide (e.role<roles.length) && e.cert.ok C (e.ends roles).1 (e.ends roles).2 e.x e.x' e.y e.y'

/-- A chart covered by certified rectangles of cells and special cells: every point is seen from
the guard segment of one entry or lies in a special closed cell. -/
theorem cover (G : Good C X Y s A) (hnd : ∀ t∈C.tiles, t.1<t.2.1 ∧ t.2.2.1<t.2.2.2)
    {roles : List (List Index)} {rects : List Entry} {special : List (Nat × Nat)}
    (hok : rects.all (Entry.good C roles)=true)
    (hcomp : ∀ t∈C.tiles, ∀ i j, t.1 ≤ i → i<t.2.1 → t.2.2.1≤j → j<t.2.2.2 →
      (i,j)∈special ∨ ∃ e∈rects, e.x ≤ i ∧ i+1≤e.x' ∧ e.y≤j ∧ j+1≤e.y')
    {z : Point} (hz : z∈(C.poly X Y).filled) :
    (∃ e∈rects, e.role<roles.length ∧
      ∀ g∈ArtGallery.segment (gridPt X Y (e.ends roles).1) (gridPt X Y (e.ends roles).2), (C.poly X Y).Sees g z) ∨
    ∃ c∈special, z∈Rect (X.getD c.1 0) (X.getD (c.1+1) 0) (Y.getD c.2 0) (Y.getD (c.2+1) 0) := by
  obtain ⟨t,ht,i,j,i0,i1,j0,j1,hzc⟩ := point_cell G hnd hz
  rcases hcomp t ht i j i0 i1 j0 j1 with sp|⟨e,he,e0,e1,e2,e3⟩
  · exact Or.inr ⟨(i,j),sp,hzc⟩
  · left
    have hg := List.all_eq_true.mp hok e he
    simp only [Entry.good,Bool.and_eq_true,decide_eq_true_eq] at hg
    obtain ⟨hk,hc⟩ := hg
    refine ⟨e,he,hk,fun g hg => Cert.sound G hc hg ?_⟩
    obtain ⟨z0,z1,z2,z3⟩ := hzc
    have lx := G.lx; have ly := G.ly
    have idx := G.tileIdx t ht
    unfold Cert.ok at hc
    split at hc
    · simp at hc
    · simp only [Bool.and_eq_true,decide_eq_true_eq] at hc
      obtain ⟨-,-,-,-,-,ex1,-,ey1⟩ := hc.2
      refine ⟨(lev_le G.hx (by omega) e0).trans z0,z1.trans (lev_le G.hx (by omega) e1),
        (lev_le G.hy (by omega) e2).trans z2,z3.trans (lev_le G.hy (by omega) e3)⟩

end Cover

end ArtGallery.Orthogonal.BoundaryPoint.CoverChain
end
