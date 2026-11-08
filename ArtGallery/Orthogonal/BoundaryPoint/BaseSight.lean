module

public import ArtGallery.Orthogonal.BoundaryPoint.CoverAssume

/-! # A base guard sees a wing cell through the door

A guard `B` below the door line `y = 1` whose sightline to a wing point `z` crosses the door
segment `[(0,1),(W,1)]` at `d` sees `z` when it sees the door point `d` (in the hub) and the door
segment sees `z` in the wing by a chain certificate. The assumed window ends of that certificate
hold for `d` as soon as they hold for `B`: `d`, `B` and `z` are collinear, with `d` between. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.BaseSight
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert CoverChain CoverAssume ArtGallery.Orthogonal.Hard

theorem det_on_line (B z w : Point) (t : ℝ) :
    ArtGallery.det (Geometry.lerp B z t) z w=(1-t)*ArtGallery.det B z w := by
  simp only [ArtGallery.det,Geometry.lerp]; ring

theorem lerp_lerp_right (p q : Point) (τ u : ℝ) :
    Geometry.lerp (Geometry.lerp p q τ) q u=Geometry.lerp p q (τ+u*(1-τ)) := by
  simp only [Geometry.lerp]; ext <;> simp only <;> ring

/-- A segment through a point of it splits into the two sub-segments. -/
theorem segment_split {p q x : Point} (hx : x∈ArtGallery.segment p q) :
    ArtGallery.segment p q⊆ArtGallery.segment p x∪ArtGallery.segment x q := by
  obtain ⟨τ,hτ0,hτ1,rfl⟩ := Geometry.mem_segment_iff_lerp.mp hx
  intro y hy
  obtain ⟨s,hs0,hs1,rfl⟩ := Geometry.mem_segment_iff_lerp.mp hy
  by_cases hsτ : s≤τ
  · left
    rcases eq_or_lt_of_le hτ0 with hτ|hτ
    · have : s=0 := by linarith
      subst this; rw [← hτ]
      exact Geometry.mem_segment_iff_lerp.mpr ⟨0,le_rfl,zero_le_one,by simp [Geometry.lerp]⟩
    · refine Geometry.mem_segment_iff_lerp.mpr ⟨s/τ,div_nonneg hs0 hτ.le,(div_le_one hτ).2 hsτ,?_⟩
      simp only [Geometry.lerp]; ext <;> simp only <;> field_simp <;> ring
  · right
    push Not at hsτ
    have hτ1' : τ<1 := lt_of_lt_of_le hsτ hs1
    refine Geometry.mem_segment_iff_lerp.mpr ⟨(s-τ)/(1-τ),div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).2 (by linarith),?_⟩
    rw [lerp_lerp_right]
    congr 1
    have : (s-τ)/(1-τ)*(1-τ)=s-τ := div_mul_cancel₀ _ (by linarith)
    linarith

/-- Splitting a sightline at an intermediate point. -/
theorem sees_split {P : Polygon} {B z d : Point} (hd : d∈ArtGallery.segment B z) (h1 : P.Sees B d)
    (h2 : P.Sees d z) : P.Sees B z := fun _ hy =>
  (segment_split hd hy).elim (fun h => h1 h) (fun h => h2 h)

section
variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

/-- A guard below the door sees a cell point whose sightline crosses the door, given a chain
certificate from the door segment with assumed ends satisfied by the guard. -/
theorem base_sees (G : Good C X Y s A) {P : Polygon} (sub : (C.poly X Y).filled⊆P.filled)
    {W : ℝ} {dl dr : Index} (hdl : gridPt X Y dl=((0:ℝ),(1:ℝ))) (hdr : gridPt X Y dr=(W,1))
    {B : Point} (hBy : B.2<1) (hdoor : ∀ d∈ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1), P.Sees B d)
    {x x' y y' : Nat} {c : CertA} (hc : c.ok C dl dr x x' y y'=true)
    {z : Point} (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0)) (hzy : 1≤z.2)
    (cross0 : 0≤ArtGallery.det B z ((0:ℝ),(1:ℝ))) (crossW : ArtGallery.det B z (W,1)≤0)
    (hA : ∀ e∈c.assumed, Holds X Y B z e) : P.Sees B z := by
  obtain ⟨t,t0,t1,ey,elo,ehi⟩ := cross_horizontal (g:=B) (z:=z) (c:=1) (lo:=0) (hi:=W)
    (by linarith) hBy.le hzy cross0 crossW
  set d := Geometry.lerp B z t with hd
  have dseg : d∈ArtGallery.segment B z := Geometry.mem_segment_iff_lerp.mpr ⟨t,t0,t1,rfl⟩
  have hW : 0≤W := le_trans elo ehi
  have ddoor : d∈ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1) := by
    rcases eq_or_lt_of_le hW with e|pos
    · refine ⟨0,le_rfl,zero_le_one,?_⟩
      ext
      · simp only; rw [← e] at ehi; linarith
      · simp only; linarith
    · refine ⟨d.1/W,div_nonneg elo hW,(div_le_one pos).mpr ehi,?_⟩
      ext
      · simp only; field_simp; ring
      · simp only; linarith
  have dgrid : d∈ArtGallery.segment (gridPt X Y dl) (gridPt X Y dr) := by rw [hdl,hdr]; exact ddoor
  have wing : (C.poly X Y).Sees d z := by
    apply CertA.sound G hc dgrid hz
    intro e he
    have h := hA e he
    simp only [Holds] at h ⊢
    rw [hd,det_on_line]
    have : 0≤1-t := by linarith
    calc (0:ℝ) ≤ (1-t)*((if e.2 then 1 else -1)*ArtGallery.det B z (gridPt X Y e.1)) := mul_nonneg this h
      _ = _ := by ring
  exact sees_split dseg (hdoor d ddoor) (fun p hp => sub (wing hp))

end

end ArtGallery.Orthogonal.BoundaryPoint.BaseSight
end
