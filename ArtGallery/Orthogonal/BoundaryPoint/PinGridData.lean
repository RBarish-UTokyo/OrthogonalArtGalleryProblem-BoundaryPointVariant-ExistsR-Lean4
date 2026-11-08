module

public import ArtGallery.Orthogonal.BoundaryPoint.GridParity
public import ArtGallery.Orthogonal.BoundaryPoint.PerpendicularPin

/-! # Discrete geometry of a shaft-and-cap pin on a room grid

The coordinate chart may exchange the two axes and reverse either direction.
Each integer atom is a grid line or the open interval on one of its sides.
All contact and boundary-clearance predicates therefore transfer to any
ordered realization of the grid. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PinGridData
open Set GridAtom GridParity RoomGrid CorridorProgram PerpendicularPin ArtGallery.Orthogonal.Hard

def signR (neg : Bool) (x : ℝ) := if neg then -x else x
def signZ (neg : Bool) (x : Nat) : Int := if neg then -(x:Int) else (x:Int)
def component {α} (swap : Bool) (p : α × α) : α := if swap then p.2 else p.1
def coord (axis neg : Bool) (xs ys : List ℝ) (i : Nat) : ℝ := signR neg ((if axis then ys else xs).getD i 0)
def code (axis neg : Bool) (x y : Nat) : Int := signZ neg (component axis (x,y))
def ptCoord (axis neg : Bool) (z : Point) : ℝ := signR neg (component axis z)

private theorem signed_compare {xs : List ℝ} (hx : xs.IsChain (· < ·))
    (neg : Bool) {i : Nat} (hi : i<xs.length) (z : ℝ) :
    (signR neg (xs.getD i 0) ≤ signR neg z ↔ signZ neg (line i) ≤ signZ neg (atom z xs)) ∧
    (signR neg z ≤ signR neg (xs.getD i 0) ↔ signZ neg (atom z xs) ≤ signZ neg (line i)) ∧
    (signR neg z = signR neg (xs.getD i 0) ↔ signZ neg (atom z xs) = signZ neg (line i)) := by
  cases neg <;> simp only [signR,signZ,Bool.false_eq_true,ite_false,ite_true,
    neg_le_neg_iff,neg_inj,Int.ofNat_le,Int.natCast_inj]
  · exact ⟨line_le hx hi z,le_line hx hi z,(compare_line hx hi z).2⟩
  · exact ⟨le_line hx hi z,line_le hx hi z,(compare_line hx hi z).2⟩

theorem coord_compare {xs ys : List ℝ} (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    (axis neg : Bool) {i : Nat} (hi : i < (if axis then ys else xs).length) (z : Point) :
    let a := code axis neg (atom z.1 xs) (atom z.2 ys)
    let b := signZ neg (line i)
    let v := coord axis neg xs ys i
    let t := ptCoord axis neg z
    (v ≤ t ↔ b ≤ a) ∧ (t ≤ v ↔ a ≤ b) ∧ (t=v ↔ a=b) := by
  cases axis with
  | false => exact signed_compare hx neg hi z.1
  | true => exact signed_compare hy neg hi z.2

def axisPoint (swap : Bool) (t n : Nat) : Index := if swap then (n,t) else (t,n)

theorem chart_point (f : Frame) (xs ys : List ℝ) (t n : Nat) :
    f.pt (gridPt xs ys (axisPoint f.swap t n)) =
      (coord f.swap f.negT xs ys t,coord (!f.swap) f.negN xs ys n) := by
  cases f with | mk s a b => cases s <;> rfl

theorem chart_components (f : Frame) (z : Point) :
    f.pt z=(ptCoord f.swap f.negT z,ptCoord (!f.swap) f.negN z) := by
  cases f with | mk s a b => cases s <;> rfl

theorem frame_injective (f : Frame) : Function.Injective f.pt := by
  rcases f with ⟨s,nt,nn⟩
  intro a b h
  rcases a with ⟨x,y⟩; rcases b with ⟨u,v⟩
  cases s <;> cases nt <;> cases nn <;> simpa [Frame.pt,and_comm] using h

theorem frame_mem_segment {g a b : Point} (f : Frame)
    (h : f.pt g ∈ segment (f.pt a) (f.pt b)) : g ∈ segment a b := by
  obtain ⟨s,hs,hs',he⟩ := h
  refine ⟨s,hs,hs',frame_injective f ?_⟩
  rw [he]
  rcases f with ⟨sw,nt,nn⟩
  cases sw <;> cases nt <;> cases nn <;> ext <;> simp [Frame.pt] <;> ring

def tile (xs ys : List ℝ) (r : Rect Nat) : Set Point :=
  ChimneyRegion.cell (xs.getD r.1 0) (xs.getD r.2.1 0) (ys.getD r.2.2.1 0) (ys.getD r.2.2.2 0)

theorem closed_tiles (xs ys : List ℝ) (rs : List (Rect Nat)) : IsClosed (cellsR xs ys rs) := by
  induction rs with
  | nil => simpa [cellsR] using (isClosed_empty : IsClosed (∅ : Set Point))
  | cons r rs ih =>
    have eq : cellsR xs ys (r::rs) = tile xs ys r ∪ cellsR xs ys rs := by
      ext z
      simp [cellsR,tile,ChimneyRegion.cell]
    rw [eq]
    exact (ChimneyRegion.cell_closed _ _ _ _).union ih

def rest (r : Rect Nat) (rs : List (Rect Nat)) := rs.filter (fun q => q != r)

theorem split_tile (xs ys : List ℝ) {r} {rs : List (Rect Nat)} (hr : r∈rs) :
    cellsR xs ys rs=tile xs ys r ∪ cellsR xs ys (rest r rs) := by
  ext z
  constructor
  · rintro ⟨q,hq,a⟩
    by_cases e : q=r
    · subst q; exact Or.inl a
    · exact Or.inr ⟨q,by simp [rest,hq,e],a⟩
  · rintro (h|⟨q,hq,h⟩)
    · exact ⟨r,hr,h⟩
    · exact ⟨q,(List.mem_filter.mp hq).1,h⟩

def ValidBox (nx ny : Nat) (r : Rect Nat) : Prop :=
  r.1<nx ∧ r.2.1<nx ∧ r.2.2.1<ny ∧ r.2.2.2<ny

theorem tile_iff {xs ys : List ℝ} (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    {r : Rect Nat} (h : ValidBox xs.length ys.length r) (z : Point) :
    z ∈ tile xs ys r ↔ inBox (atom z.1 xs) (atom z.2 ys) r=true := by
  unfold tile ChimneyRegion.cell inBox
  simp only [Set.mem_ofPred_eq,decide_eq_true_eq]
  rw [line_le hx h.1,le_line hx h.2.1,line_le hy h.2.2.1,le_line hy h.2.2.2]

structure Pin where
  frame : Frame
  low : Nat
  high : Nat
  floor : Nat
  nearS : Nat
  farS : Nat
  farC : Nat
  nearC : Nat
  top : Nat
  clear : Nat
  shaft : Rect Nat
  cap : Rect Nat

def Pin.T (p : Pin) := signZ p.frame.negT
def Pin.N (p : Pin) := signZ p.frame.negN
def Pin.tval (p : Pin) := coord p.frame.swap p.frame.negT
def Pin.nval (p : Pin) := coord (!p.frame.swap) p.frame.negN
def Pin.point (p : Pin) := axisPoint p.frame.swap
def Pin.shaftTips (p : Pin) := [p.point p.low p.farS,p.point p.high p.farS]
def Pin.witnesses (p : Pin) := p.shaftTips ++ [p.point p.farC p.floor]
def Pin.spot (p : Pin) := (p.point p.low p.floor,p.point p.high p.floor)

def Pin.Valid (p : Pin) (nx ny : Nat) (rs : List (Rect Nat)) : Prop :=
  let t := if p.frame.swap then ny else nx
  let n := if p.frame.swap then nx else ny
  (∀ i ∈ [p.low,p.high,p.farC,p.nearC], i<t) ∧
  (∀ i ∈ [p.floor,p.nearS,p.farS,p.top,p.clear], i<n) ∧
  p.shaft∈rs ∧ p.cap∈rs ∧ p.N (line p.nearS) ≠ p.N (line p.farS) ∧
  p.T (line p.farC)<p.T (line p.nearC) ∧
  (∀ q ∈ p.shaftTips, inBox (line q.1) (line q.2) p.shaft=true) ∧
  (let q := p.point p.farC p.floor; inBox (line q.1) (line q.2) p.cap=true)
instance (p : Pin) (nx ny : Nat) (rs : List (Rect Nat)) : Decidable (p.Valid nx ny rs) := by
  unfold Pin.Valid; infer_instance

def Pin.At (p : Pin) (rs : List (Rect Nat)) (l : List Index) (X Y : Nat) : Prop :=
  let t := code p.frame.swap p.frame.negT X Y
  let n := code (!p.frame.swap) p.frame.negN X Y
  let between := p.T (line p.low)≤t ∧ t≤p.T (line p.high)
  let h := p.N (line p.floor)
  (inBox X Y p.shaft=true → between) ∧
  (inBox X Y p.shaft=true → n≠p.N (line p.nearS) → (rest p.shaft rs).any (inBox X Y)=false) ∧
  (inBox X Y p.cap=true → ¬between) ∧
  (inBox X Y p.cap=true → (rest p.cap rs).any (inBox X Y)=true →
    t=p.T (line p.nearC) ∧ h≤n ∧ n≤p.N (line p.top)) ∧
  (between → h<n → n<p.N (line p.clear) → boundaryB l X Y=false)

instance (p : Pin) (rs : List (Rect Nat)) (l : List Index) (X Y : Nat) : Decidable (p.At rs l X Y) := by
  unfold Pin.At; infer_instance

end ArtGallery.Orthogonal.BoundaryPoint.PinGridData
end
