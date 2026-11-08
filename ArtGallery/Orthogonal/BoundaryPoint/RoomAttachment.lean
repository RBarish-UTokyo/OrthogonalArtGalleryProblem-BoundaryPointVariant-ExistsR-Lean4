module

public import ArtGallery.Orthogonal.BoundaryPoint.WindowBoundary
public import ArtGallery.Orthogonal.BoundaryPoint.SingleWindow
public import ArtGallery.Vis.API

/-! # Boundary viewers of a marked room after attachment

One witness invisible from the entire closed window confines its viewer to
the room. All sightlines to the remaining marked points then restrict to the
local polygon. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomAttachment
open Set

structure Joined (P room : Polygon) (a b : Point) where
  rest : Set Point
  closed : IsClosed rest
  fill : P.filled=room.filled∪rest
  contact : room.filled∩rest=ArtGallery.segment a b

theorem Joined.local_view {P room : Polygon} {a b w g : Point} (d : Joined P room a b)
    (hw : w∈room.filled) (miss : ∀ q∈ArtGallery.segment a b, ¬room.Sees w q)
    (seen : P.Sees g w) : g∈room.filled ∧ g∉d.rest ∧ room.Sees g w := by
  have convex : Convex ℝ (room.filled∩d.rest) := d.contact ▸ Geometry.segment_convex _ _
  have away : g∉d.rest := by
    intro hr
    obtain ⟨q,hq,_,hq'⟩ := SingleWindow.exists_visible_window_point d.fill d.closed convex
      hw hr (Polygon.sees_comm.mp seen)
    exact miss q (d.contact ▸ hq) hq'
  have dec : g∈room.filled ∪ d.rest := d.fill ▸ seen (Geometry.left_mem_segment g w)
  have hg := dec.resolve_right away
  exact ⟨hg,away,(SingleWindow.sees_iff d.fill d.closed convex hg hw).mp seen⟩

theorem Joined.pin {P room : Polygon} {a b g : Point} (d : Joined P room a b)
    (simple : P.Simple) (localSimple : room.Simple) (boundary : g∈P.boundary)
    {W : List Point} {spot : Set Point} (ne : W≠[])
    (inside : ∀ w∈W, w∈room.filled)
    (miss : ∀ w∈W, ∀ q∈ArtGallery.segment a b, ¬room.Sees w q)
    (localize : ∀ p∈room.boundary, (∀ w∈W, room.Sees p w) → p∈spot)
    (seen : ∀ w∈W, P.Sees g w) : g∈spot ∧ g∉d.rest := by
  obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil W ne
  have view := d.local_view (inside _ hw) (miss _ hw) (seen _ hw)
  have sub : room.filled ⊆ P.filled := by rw [d.fill]; exact subset_union_left
  have bd := WindowBoundary.restrict_guard localSimple simple sub boundary view.1
  exact ⟨localize g bd (fun v hv => (d.local_view (inside _ hv) (miss _ hv) (seen _ hv)).2.2),view.2.1⟩

end ArtGallery.Orthogonal.BoundaryPoint.RoomAttachment
end
