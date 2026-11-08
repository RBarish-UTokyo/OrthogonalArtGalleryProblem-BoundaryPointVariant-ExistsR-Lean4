module

public import ArtGallery.Orthogonal.BoundaryPoint.PinGridData

/-! # Soundness of a grid pin certificate in the filled polygon -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PinGridData
open Set GridAtom GridParity GridPins RoomGrid CorridorProgram PerpendicularPin ArtGallery.Orthogonal.Hard

private theorem order_axis {xs : List ℝ} (hx : xs.IsChain (· < ·)) (neg : Bool)
    {a b : Nat} (ha : a<xs.length) (hb : b<xs.length) :
    signR neg (xs.getD a 0) < signR neg (xs.getD b 0) ↔ signZ neg (line a) < signZ neg (line b) := by
  have ab := (strictMonoOn_getD hx).lt_iff_lt (a := a) (b := b) ha hb
  have ba := (strictMonoOn_getD hx).lt_iff_lt (a := b) (b := a) hb ha
  cases neg <;> simp only [signR,signZ,Bool.false_eq_true,ite_false,ite_true,neg_lt_neg_iff,Int.ofNat_lt]
  · exact ab.trans (by unfold line; omega)
  · exact ba.trans (by unfold line; omega)

theorem order_coord {xs ys : List ℝ} (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    (axis neg : Bool) {a b : Nat}
    (ha : a<(if axis then ys else xs).length) (hb : b<(if axis then ys else xs).length) :
    coord axis neg xs ys a < coord axis neg xs ys b ↔ signZ neg (line a) < signZ neg (line b) := by
  cases axis with
  | false => exact order_axis hx neg ha hb
  | true => exact order_axis hy neg ha hb

theorem at_node {xs ys : List ℝ} (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    {i : Index} (hi : small xs.length ys.length i) :
    (atom (gridPt xs ys i).1 xs,atom (gridPt xs ys i).2 ys) = (line i.1,line i.2) :=
  Prod.ext ((compare_line hx hi.1 _).2.mp rfl) ((compare_line hy hi.2 _).2.mp rfl)

theorem localizes {P : Polygon} {xs ys : List ℝ} (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    {rs : List (Rect Nat)} {l : List Index}
    (hfilled : P.filled=cellsR xs ys rs)
    (hboundary : ∀ g∈P.boundary, boundaryB l (atom g.1 xs) (atom g.2 ys)=true)
    (hRs : ∀ r∈rs, ValidBox xs.length ys.length r)
    (p : Pin) (hv : p.Valid xs.length ys.length rs)
    (hNodes : ∀ w∈p.witnesses, small xs.length ys.length w)
    (hA : ∀ X ≤ 2*xs.length, ∀ Y ≤ 2*ys.length, p.At rs l X Y)
    (hGap : (p.tval xs ys p.high-p.tval xs ys p.farC)*(p.nval xs ys p.top-p.nval xs ys p.floor) <
      (p.nval xs ys p.clear-p.nval xs ys p.floor)*(p.tval xs ys p.nearC-p.tval xs ys p.farC))
    {g : Point} (hg : g∈P.boundary) (sees : ∀ w∈p.witnesses, P.Sees g (gridPt xs ys w)) :
    g ∈ segment (gridPt xs ys p.spot.1) (gridPt xs ys p.spot.2) := by
  rcases hv with ⟨hts,hns,hS,hC,hSF,hCF,hW,hW'⟩
  let tlist := [p.low,p.high,p.farC,p.nearC]
  let nlist := [p.floor,p.nearS,p.farS,p.top,p.clear]
  have tb {i} (h : i∈tlist) : i<(if p.frame.swap then ys else xs).length := by
    have u := hts _ h
    cases e : p.frame.swap <;> simpa only [e,Bool.false_eq_true,ite_false,ite_true] using u
  have nb {i} (h : i∈nlist) : i<(if !p.frame.swap then ys else xs).length := by
    have u := hns _ h
    cases e : p.frame.swap <;> simpa only [e,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] using u
  let tc := fun i => p.tval xs ys i; let nc := fun i => p.nval xs ys i
  let tx := fun z : Point => code p.frame.swap p.frame.negT (atom z.1 xs) (atom z.2 ys)
  let nz := fun z : Point => code (!p.frame.swap) p.frame.negN (atom z.1 xs) (atom z.2 ys)
  have tr {i} (h : i∈tlist) (z : Point) :
      (tc i≤(p.frame.pt z).1 ↔ p.T (line i)≤tx z) ∧
      ((p.frame.pt z).1≤tc i ↔ tx z≤p.T (line i)) ∧ ((p.frame.pt z).1=tc i ↔ tx z=p.T (line i)) := by
    rw [chart_components]
    exact coord_compare hx hy _ _ (tb h) z
  have nr {i} (h : i∈nlist) (z : Point) :
      (nc i≤(p.frame.pt z).2 ↔ p.N (line i)≤nz z) ∧
      ((p.frame.pt z).2≤nc i ↔ nz z≤p.N (line i)) ∧ ((p.frame.pt z).2=nc i ↔ nz z=p.N (line i)) := by
    rw [chart_components]
    exact coord_compare hx hy _ _ (nb h) z
  have nt (i j) (hi : i∈nlist) (hj : j∈nlist) :
      nc i<nc j ↔ p.N (line i)<p.N (line j) := order_coord hx hy _ _ (nb hi) (nb hj)
  have hn : nc p.nearS≠nc p.farS := by
    rcases lt_or_gt_of_ne hSF with h|h
    · exact ((nt _ _ (by simp [nlist]) (by simp [nlist])).2 h).ne
    · exact ((nt _ _ (by simp [nlist]) (by simp [nlist])).2 h).ne'
  have hd : tc p.farC<tc p.nearC := (order_coord hx hy _ _ (tb (i := p.farC) (by simp [tlist]))
    (tb (i := p.nearC) (by simp [tlist]))).2 hCF
  have fact (z : Point) := hA (atom z.1 xs) (atom_bound _ _) (atom z.2 ys) (atom_bound _ _)
  have hrest (r) (z : Point) : z∈cellsR xs ys (rest r rs) ↔
      (rest r rs).any (inBox (atom z.1 xs) (atom z.2 ys))=true :=
    cells_iff hx hy (fun q h => hRs q (List.mem_filter.mp h).1) z
  have sh (z : Point) := tile_iff hx hy (hRs p.shaft hS) z
  have cp (z : Point) := tile_iff hx hy (hRs p.cap hC) z
  have csh : IsClosed (tile xs ys p.shaft) := ChimneyRegion.cell_closed _ _ _ _
  have ccp : IsClosed (tile xs ys p.cap) := ChimneyRegion.cell_closed _ _ _ _
  have joinS := hfilled.trans (split_tile xs ys hS)
  have joinC := hfilled.trans (split_tile xs ys hC)
  have witness (r : Rect Nat) (hr : r∈rs) (i : Index) (hi : i∈p.witnesses)
      (hf : inBox (line i.1) (line i.2) r=true) : gridPt xs ys i∈tile xs ys r := by
    apply (tile_iff hx hy (hRs _ hr) _).2
    have h := at_node hx hy (hNodes i hi)
    exact (congrArg (fun z : Nat × Nat => inBox z.1 z.2 r) h).trans hf
  have m0 : p.point p.low p.farS ∈ p.witnesses := by simp [Pin.witnesses,Pin.shaftTips]
  have m1 : p.point p.high p.farS ∈ p.witnesses := by simp [Pin.witnesses,Pin.shaftTips]
  have m2 : p.point p.farC p.floor ∈ p.witnesses := by simp [Pin.witnesses,Pin.shaftTips]
  have bounds : tc p.low≤(p.frame.pt g).1 ∧ (p.frame.pt g).1≤tc p.high := by
    apply tangent hn csh (closed_tiles _ _ _) joinS
    · intro q hq
      have h := (fact q).1 ((sh q).1 hq)
      exact ⟨(tr (by simp [tlist]) q).1.mpr h.1,(tr (by simp [tlist]) q).2.1.mpr h.2⟩
    · intro q hq
      apply (nr (by simp [nlist]) q).2.2.mpr
      by_contra! h
      have hno := (fact q).2.1 ((sh q).1 hq.1) h
      rw [(hrest _ q).1 hq.2] at hno
      contradiction
    · exact witness _ hS _ m0 (hW _ (by simp [Pin.shaftTips]))
    · exact witness _ hS _ m1 (hW _ (by simp [Pin.shaftTips]))
    · exact chart_point _ _ _ _ _
    · exact chart_point _ _ _ _ _
    · exact Or.inl hg
    · exact sees _ m0
    · exact sees _ m1
  have between := And.intro ((tr (by simp [tlist]) g).1.mp bounds.1)
    ((tr (by simp [tlist]) g).2.1.mp bounds.2)
  have outCap : g∈cellsR xs ys (rest p.cap rs) := by
    have h : g∈P.filled := Or.inl hg
    rw [joinC] at h
    exact h.resolve_left (fun h' => (fact g).2.2.1 ((cp g).1 h') between)
  have boundN : nc p.floor≤(p.frame.pt g).2 ∧
      ((p.frame.pt g).2-nc p.floor)*(tc p.nearC-tc p.farC)≤(tc p.high-tc p.farC)*(nc p.top-nc p.floor) := by
    apply normal_bound hd ccp (closed_tiles _ _ _) joinC
    · intro q hq
      obtain ⟨ht,hl,hu⟩ := (fact q).2.2.2.1 ((cp q).1 hq.1) ((hrest _ q).1 hq.2)
      exact ⟨(tr (by simp [tlist]) q).2.2.mpr ht,(nr (by simp [nlist]) q).1.mpr hl,
        (nr (by simp [nlist]) q).2.1.mpr hu⟩
    · exact witness _ hC _ m2 hW'
    · exact chart_point _ _ _ _ _
    · exact outCap
    · exact sees _ m2
    · exact bounds.2
  have orClear : (p.frame.pt g).2=nc p.floor ∨ nc p.clear≤(p.frame.pt g).2 := by
    by_cases e : (p.frame.pt g).2=nc p.floor
    · exact Or.inl e
    right
    apply (nr (by simp [nlist]) g).1.mpr
    by_contra! hlt
    have hgt := lt_of_le_of_ne ((nr (by simp [nlist]) g).1.mp boundN.1)
      (Ne.symm (fun h => e ((nr (by simp [nlist]) g).2.2.mpr h)))
    have hno := (fact g).2.2.2.2 between hgt hlt
    rw [hboundary g hg] at hno
    contradiction
  have eqN := force_level (sub_pos.mpr hd) boundN.1 orClear boundN.2 hGap
  apply frame_mem_segment p.frame
  change p.frame.pt g ∈ segment (p.frame.pt (gridPt xs ys (axisPoint p.frame.swap p.low p.floor)))
    (p.frame.pt (gridPt xs ys (axisPoint p.frame.swap p.high p.floor)))
  rw [chart_point,chart_point]
  exact GridPins.horizontal rfl eqN bounds.1 bounds.2

def pinRow (pins : List Pin) (rs : List (Rect Nat)) (l : List Index) (X ny : Nat) : Bool :=
  pins.all fun p => (List.range (2*ny+1)).all (fun Y => decide (p.At rs l X Y))

theorem at_of_rows {pins : List Pin} {rs : List (Rect Nat)} {l : List Index} {nx ny : Nat}
    (rows : ∀ i : Fin (2*nx+1), pinRow pins rs l i.val ny=true) {p : Pin} (hp : p∈pins) :
    ∀ X ≤ 2*nx, ∀ Y ≤ 2*ny, p.At rs l X Y := by
  intro X hX Y hY
  have h := rows ⟨X,Nat.lt_succ_of_le hX⟩
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h _ hp) _ (List.mem_range.mpr (Nat.lt_succ_of_le hY)))

end ArtGallery.Orthogonal.BoundaryPoint.PinGridData
end
