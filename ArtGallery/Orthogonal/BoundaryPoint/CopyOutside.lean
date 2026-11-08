module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomAttachment
public import ArtGallery.Jordan.Filled

/-! # Guards outside a wing that cannot see above its door line

A polygon joined to a wing along a horizontal door at height `1`: every sight
line from outside into the wing crosses the door. A guard outside the wing at
height at least `1`, not on the door, sees no wing point above the door line.
A guard in a second wing, joined along its own door at height `1`, sees no
point of the first wing off the door line: its sight line would meet the door
line twice. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyOutside
open Set RoomAttachment

/-- Two distinct points of a segment on the line `y=1` force the far end onto it. -/
theorem two_on_line {g z p q : Point} (hp : p∈ArtGallery.segment g z) (hq : q∈ArtGallery.segment g z)
    (hp1 : p.2=1) (hq1 : q.2=1) (ne : p≠q) : z.2=1 := by
  obtain ⟨t,-,-,rfl⟩ := hp
  obtain ⟨u,-,-,rfl⟩ := hq
  simp only at hp1 hq1
  have htu : t≠u := by intro e; subst e; exact ne rfl
  have : (t-u)*(z.2-g.2)=0 := by linarith
  rcases mul_eq_zero.mp this with h|h
  · exact absurd (sub_eq_zero.mp h) htu
  · have : z.2=g.2 := by linarith
    rw [this]; rw [this] at hp1; linarith

theorem sub_segment {g z p : Point} (hp : p∈ArtGallery.segment g z) :
    ArtGallery.segment p z⊆ArtGallery.segment g z :=
  Geometry.segment_subset_of_convex (Geometry.segment_convex g z) hp (Geometry.right_mem_segment g z)

/-- A guard outside the wing, at or above the door line and not on the door. -/
theorem level_guard {P W : Polygon} {a b : Point} (J : Joined P W a b) (ha : a.2=1) (hb : b.2=1)
    {g z : Point} (hg : g∈J.rest) (hz : z∈W.filled) (hz1 : 1<z.2) (hg1 : 1≤g.2)
    (off : g∉ArtGallery.segment a b) : ¬P.Sees g z := by
  intro sees
  obtain ⟨p,hp,hpW,hpR⟩ := SingleWindow.segment_meets_window J.closed (Jordan.isClosed_filled W) hg hz
    (by rw [Set.union_comm,←J.fill]; exact sees)
  have hseam : p∈ArtGallery.segment a b := by rw [←J.contact]; exact ⟨hpR,hpW⟩
  have hp1 : p.2=1 := by
    obtain ⟨t,-,-,rfl⟩ := hseam; simp only; rw [ha,hb]; ring
  obtain ⟨t,t0,t1,rfl⟩ := hp
  simp only at hp1
  have e : (1-t)*(g.2-1)+t*(z.2-1)=0 := by linarith
  have a1 : 0≤(1-t)*(g.2-1) := mul_nonneg (by linarith) (by linarith)
  have a2 : 0≤t*(z.2-1) := mul_nonneg t0 (by linarith)
  have tz : t=0 := by
    have : t*(z.2-1)=0 := by linarith
    rcases mul_eq_zero.mp this with h|h
    · exact h
    · linarith
  subst tz
  apply off
  convert hseam using 1; ext <;> simp

/-- A guard in a second wing joined along its own door at height `1`. -/
theorem two_seams {P W W' : Polygon} {a b a' b' : Point} (J : Joined P W a b) (J' : Joined P W' a' b')
    (ha : a.2=1) (hb : b.2=1) (ha' : a'.2=1) (hb' : b'.2=1) (disj : Disjoint W.filled W'.filled)
    {g z : Point} (hg : g∈W'.filled) (hz : z∈W.filled) (hz1 : z.2≠1) : ¬P.Sees g z := by
  intro sees
  have zP : z∈P.filled := sees (Geometry.right_mem_segment g z)
  have zR' : z∈J'.rest := by
    rw [J'.fill] at zP
    rcases zP with h|h
    · exact absurd h (Set.disjoint_left.mp disj hz)
    · exact h
  obtain ⟨p',hp',hp'W,hp'R⟩ := SingleWindow.segment_meets_window (Jordan.isClosed_filled W') J'.closed hg zR'
    (by rw [←J'.fill]; exact sees)
  have hseam' : p'∈ArtGallery.segment a' b' := by rw [←J'.contact]; exact ⟨hp'W,hp'R⟩
  have p'1 : p'.2=1 := by
    obtain ⟨t,-,-,rfl⟩ := hseam'; simp only; rw [ha',hb']; ring
  have p'W : p'∉W.filled := fun h => Set.disjoint_left.mp disj h hp'W
  have p'R : p'∈J.rest := by
    have := sees hp'
    rw [J.fill] at this
    rcases this with h|h
    · exact absurd h p'W
    · exact h
  obtain ⟨p,hp,hpR,hpW⟩ := SingleWindow.segment_meets_window J.closed (Jordan.isClosed_filled W) p'R hz
    (by rw [Set.union_comm,←J.fill]; exact Set.Subset.trans (sub_segment hp') sees)
  have hseam : p∈ArtGallery.segment a b := by rw [←J.contact]; exact ⟨hpW,hpR⟩
  have p1 : p.2=1 := by
    obtain ⟨t,-,-,rfl⟩ := hseam; simp only; rw [ha,hb]; ring
  have ne : p≠p' := by intro e; subst e; exact p'W hpW
  exact hz1 (two_on_line (sub_segment hp' hp) hp' p1 p'1 ne)

end ArtGallery.Orthogonal.BoundaryPoint.CopyOutside
end
