module

public import ArtGallery.Orthogonal.BoundaryPoint.GridParity

/-! # Boundary cells of an orthogonal grid cycle

A boundary point of a grid chart has a pair of atom codes. Along each chart
edge these codes range over a computable list. A code `2i+1` is the grid line
`i`; a code `2i+2` is the open interval between lines `i` and `i+1`. Every
boundary cell therefore lies in the closed segment between two grid nodes:
a node itself, or two consecutive nodes on one grid line. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SpanCells
open Set GridAtom GridParity RoomGrid ArtGallery.Orthogonal.Hard

/-- Lower and upper grid index of an atom code. -/
def lo (c : Nat) : Nat := (c-1)/2
def hi (c : Nat) : Nat := c/2

/-- All atom codes between two grid lines, inclusive. -/
def codes (a b : Nat) : List Nat :=
  let u := line (min a b)
  (List.range (line (max a b)-u+1)).map (u+·)

/-- Atom-code pairs of all boundary points of the cycle. -/
def cellsOf (l : List Index) : List (Nat × Nat) :=
  (List.range l.length).flatMap fun i =>
    (codes (aidx l i).1 (bidx l i).1).flatMap fun x => (codes (aidx l i).2 (bidx l i).2).map fun y => (x,y)

theorem mem_codes {a b z : Nat} (h : Between (line a) (line b) z) : z∈codes a b := by
  unfold codes
  apply List.mem_map.mpr
  refine ⟨z-line (min a b),?_,?_⟩
  · apply List.mem_range.mpr
    unfold Between line at *
    rcases le_total a b with e|e
    · simp only [min_eq_left e,max_eq_right e]; omega
    · simp only [min_eq_right e,max_eq_left e]; omega
  · unfold Between line at *
    rcases le_total a b with e|e
    · simp only [min_eq_left e]; omega
    · simp only [min_eq_right e]; omega

theorem mem_cells {l : List Index} {X Y : Nat} (h : boundaryB l X Y=true) : (X,Y)∈cellsOf l := by
  simp only [boundaryB,List.any_eq_true,List.mem_range] at h
  obtain ⟨i,hi,e⟩ := h
  have e' : Between (line (aidx l i).1) (line (bidx l i).1) X ∧ Between (line (aidx l i).2) (line (bidx l i).2) Y := by
    simpa only [onEdge,decide_eq_true_eq] using e
  exact List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,
    List.mem_flatMap.mpr ⟨X,mem_codes e'.1,List.mem_map.mpr ⟨Y,mem_codes e'.2,rfl⟩⟩⟩

/-- A cell code within the grid: a grid line or an inner open interval. -/
def Inner (n c : Nat) : Prop := 1≤c ∧ hi c<n
instance (n c : Nat) : Decidable (Inner n c) := by unfold Inner; infer_instance

theorem coordinate {xs : List ℝ} (hx : xs.IsChain (·<·)) {c : Nat} (hc : Inner xs.length c) {z : ℝ}
    (hz : atom z xs=c) : xs.getD (lo c) 0≤z ∧ z≤xs.getD (hi c) 0 := by
  have h1 : lo c<xs.length := by unfold lo; unfold Inner hi at hc; omega
  constructor
  · rw [line_le hx h1,hz]; have := hc.1; unfold line lo; omega
  · rw [le_line hx hc.2,hz]; unfold line hi; omega

/-- On a grid line the coordinate is exact. -/
theorem on_line {xs : List ℝ} (hx : xs.IsChain (·<·)) {c : Nat} (hc : Inner xs.length c) (odd : c%2=1)
    {z : ℝ} (hz : atom z xs=c) : z=xs.getD (lo c) 0 := by
  have h1 : lo c<xs.length := by unfold lo; unfold Inner hi at hc; omega
  exact ((compare_line hx h1 z).2).mpr (by rw [hz]; unfold line lo; omega)

/-- A boundary cell lies in the closed segment between its two grid nodes. -/
theorem segment_of_cell {xs ys : List ℝ} (hx : xs.IsChain (·<·)) (hy : ys.IsChain (·<·)) {c d : Nat}
    (hc : Inner xs.length c) (hd : Inner ys.length d) (axis : c%2=1 ∨ d%2=1) {z : Point}
    (zx : atom z.1 xs=c) (zy : atom z.2 ys=d) :
    z∈ArtGallery.segment (gridPt xs ys (lo c,lo d)) (gridPt xs ys (hi c,hi d)) := by
  have bx := coordinate hx hc zx
  have by' := coordinate hy hd zy
  rcases axis with o|o
  · have e := on_line hx hc o zx
    have same : lo c=hi c := by unfold lo hi; omega
    apply (segment_box (Or.inl (by simp [gridPt,same]))).mpr
    exact ⟨Or.inl ⟨le_of_eq e.symm,by simp only [gridPt]; rw [←same]; exact le_of_eq e⟩,Or.inl by'⟩
  · have e := on_line hy hd o zy
    have same : lo d=hi d := by unfold lo hi; omega
    apply (segment_box (Or.inr (by simp [gridPt,same]))).mpr
    exact ⟨Or.inl bx,Or.inl ⟨le_of_eq e.symm,by simp only [gridPt]; rw [←same]; exact le_of_eq e⟩⟩

/-- Every boundary point of a grid chart lies in a listed cell, hence on the closed segment
between two grid nodes of that cell. -/
theorem boundary_cell {xs ys : List ℝ} (hx : xs.IsChain (·<·)) (hy : ys.IsChain (·<·))
    {l : List Index} (hV : ∀ p∈l,p.1<xs.length ∧ p.2<ys.length) (ho : cyclicAxis l)
    (good : ∀ e∈cellsOf l,Inner xs.length e.1 ∧ Inner ys.length e.2 ∧ (e.1%2=1 ∨ e.2%2=1))
    {z : Point} (hz : z∈(Polygon.mk (l.map (gridPt xs ys))).boundary) :
    ∃ e∈cellsOf l,atom z.1 xs=e.1 ∧ atom z.2 ys=e.2 ∧
      z∈ArtGallery.segment (gridPt xs ys (lo e.1,lo e.2)) (gridPt xs ys (hi e.1,hi e.2)) := by
  have m := mem_cells ((boundary_iff hx hy hV ho z).mp hz)
  obtain ⟨g1,g2,g3⟩ := good _ m
  exact ⟨_,m,rfl,rfl,segment_of_cell hx hy g1 g2 g3 rfl rfl⟩

end ArtGallery.Orthogonal.BoundaryPoint.SpanCells
end
