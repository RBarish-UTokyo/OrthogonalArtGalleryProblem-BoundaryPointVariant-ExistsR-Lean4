module

public import ArtGallery.Orthogonal.BoundaryPoint.HubFloor
public import ArtGallery.Orthogonal.BoundaryPoint.HubRoles
public import ArtGallery.Orthogonal.BoundaryPoint.RealizedHub

/-! # Boundary points of the emitted gallery in a shaft column

A boundary point of the emitted gallery in the column of a base shaft lies on
the floor or at least at the low roof: below the floor only feet are filled,
and a point strictly inside the floor band and off the hub boundary is an
interior point of the gallery. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubSpots
open HubRoles HubColumns HubFloor BankCoordinates CompiledSize CatalogPlan

variable {eqs : List ETRINV.Constraint} {v : List RectContour.Vertex} {g : Nat}
variable (ne : eqs≠[]) (out : CandidateWord.vertices eqs=some (v,g))
include ne out

theorem column {q : Point} (hq : q∈(Polygon.mk (v.map ratPoint)).boundary) {x : ℚ} (hx : x∈PlacedSlots.starts eqs)
    (h0 : (x:ℝ)≤q.1) (h1 : q.1≤((x+3/2:ℚ):ℝ)) : q.2=((flo eqs:ℚ):ℝ) ∨ -6≤q.2 := by
  have placed := RealizedHub.placed ne
  have hfar : (1970:ℝ)<x := by exact_mod_cast placed.far x hx
  have hP := (GlobalShape.decomposition ne out).simple
  have qf : q∈(Polygon.mk (v.map ratPoint)).filled := Jordan.boundary_subset_filled _ hq
  -- not below the floor
  have notDeep : ¬ q.2<((flo eqs:ℚ):ℝ) := by
    intro deep
    obtain ⟨j,_,a,b⟩ := P_foot_column ne out qf deep
    have : ((fr j:ℚ):ℝ)≤100+1/1000 := by
      unfold fr door; push_cast; nlinarith [(Nat.cast_nonneg j : (0:ℝ)≤j)]
    linarith
  -- in the hub
  have hub : q∈(RealizedDoors.hub eqs).filled := by
    rcases split_filled ne out qf with h|h
    · exact h
    · exfalso; linarith [(wing_strip h).1]
  by_cases hb : q∈(RealizedDoors.hub eqs).boundary
  · rw [hub_eq] at hb
    exact HubFloor.column (rows_pos ne) (scale_bounds ne).1 placed hb hx h0 h1
  · by_contra c
    push Not at c
    -- interior point of the hub, hence of the gallery
    have open' := Jordan.isOpen_filled_sdiff_boundary (RealizedHub.production ne)
    have inP : (RealizedDoors.hub eqs).filled⊆(Polygon.mk (v.map ratPoint)).filled := by
      rw [(GlobalShape.decomposition ne out).filled]; exact Set.subset_union_left
    have cl := Jordan.boundary_subset_closure_compl hP hq
    rw [mem_closure_iff] at cl
    obtain ⟨z,hz,hzc⟩ := cl _ open' ⟨hub,hb⟩
    exact hzc (inP hz.1)

/-- A point of a shaft column at least at the low roof sees no wing point: its sight line
stays above the low roof and passes the empty strip just west of its shaft. -/
theorem high_blind {q z : Point} {x : ℚ} (hx : x∈PlacedSlots.starts eqs) (h0 : (x:ℝ)≤q.1) (hy : -6≤q.2)
    (hz : z∈EmittedGallery.unionWings eqs) : ¬(Polygon.mk (v.map ratPoint)).Sees q z := by
  intro sees
  have placed := RealizedHub.placed ne
  have hfar : (1970:ℝ)<x := by exact_mod_cast placed.far x hx
  obtain ⟨zx,zy⟩ := wing_strip hz
  set x0 : ℝ := (x:ℝ)-1
  set t : ℝ := (q.1-x0)/(q.1-z.1)
  have den : 0<q.1-z.1 := by linarith
  have t0 : 0<t := div_pos (by linarith) den
  have t1 : t≤1 := (div_le_one den).mpr (by linarith)
  let p : Point := (q.1+t*(z.1-q.1),q.2+t*(z.2-q.2))
  have pm : p∈ArtGallery.segment q z := ⟨t,t0.le,t1,rfl⟩
  have px : p.1=x0 := by
    simp only [p,t]; field_simp; ring
  have py : -6<p.2 := by
    simp only [p]; nlinarith
  obtain ⟨x',hx',a,b,_⟩ := P_shaft_column ne out (sees pm) py (by rw [px]; linarith)
  rw [px] at a b
  rcases pair_gap placed hx hx' with rfl|c|c
  · simp only [x0] at a; linarith
  · have : (x:ℝ)+10≤x' := by exact_mod_cast c
    linarith
  · have : (x':ℝ)+10≤x := by exact_mod_cast c
    push_cast at b; linarith

/-- A boundary point of the gallery in the hub and in a foot column is at most on the floor,
on the low roof, or on a cap top. -/
theorem foot {q : Point} (hq : q∈(Polygon.mk (v.map ratPoint)).boundary) (hub : q∈(RealizedDoors.hub eqs).filled)
    {m : Nat} (hm : m<(compile eqs).1.length)
    (h0 : ((fl m:ℚ):ℝ)≤q.1) (h1 : q.1≤((fr m:ℚ):ℝ)) : q.2≤((flo eqs:ℚ):ℝ) ∨ q.2=-6 ∨ q.2=1 := by
  have placed := RealizedHub.placed ne
  have hP := (GlobalShape.decomposition ne out).simple
  by_cases hb : q∈(RealizedDoors.hub eqs).boundary
  · rw [hub_eq] at hb
    exact HubFloor.foot_col (rows_pos ne) (scale_bounds ne).1 placed hb hm h0 h1
  · exfalso
    have open' := Jordan.isOpen_filled_sdiff_boundary (RealizedHub.production ne)
    have inP : (RealizedDoors.hub eqs).filled⊆(Polygon.mk (v.map ratPoint)).filled := by
      rw [(GlobalShape.decomposition ne out).filled]; exact Set.subset_union_left
    have cl := Jordan.boundary_subset_closure_compl hP hq
    rw [mem_closure_iff] at cl
    obtain ⟨z,hz,hzc⟩ := cl _ open' ⟨hub,hb⟩
    exact hzc (inP hz.1)

end ArtGallery.Orthogonal.BoundaryPoint.HubSpots
end
