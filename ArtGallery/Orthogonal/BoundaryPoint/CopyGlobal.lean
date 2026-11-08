module

public import ArtGallery.Orthogonal.BoundaryPoint.CopySpec
public import ArtGallery.Orthogonal.BoundaryPoint.GlobalBlind
public import ArtGallery.Orthogonal.BoundaryPoint.LocalWing
public import ArtGallery.Vis.CertCheckerTransfer

/-! # Copy channels in the emitted gallery

The local copy test of a channel, stated in a wing's frame (`CopySpec.Test`), is
transported to the emitted gallery: translating by minus the door abscissa puts
the wing's chart in place, the guard cover translates, and every guard other than
the base and the receiver either stands on another role's spot of the same wing or
is blind to the copy targets (`GlobalBlind`). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyGlobal
open Set ChartDrawing ContourJoin RectContour BankCoordinates CompiledSize PinTransport Hardening.Invariance
open LocalWing ArtGallery.Orthogonal.Hard

theorem choose_get {β : Type} : ∀ (ts : List Template) (value : Template → β) (i : Nat) (fb : β) {t : Template},
    ts[i]?=some t → choose ts value i fb=value t
  | [],_,_,_,_,h => by simp at h
  | t'::ts,value,0,fb,t,h => by simp at h; subst h; simp [choose]
  | t'::ts,value,i+1,fb,t,h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [choose,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel]
    exact choose_get ts value i fb h

/-- The local frame of an emitted wing, with the chart region and the rest as translates. -/
theorem frame2 {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {v g}
    (path : WingSeparation.emitted eqs r j e) (out : CandidateWord.vertices eqs=some (v,g))
    {t : Template} (ht : catalog[r.1]?=some t) :
    let s := (1:ℚ)/(scale eqs)
    let args := s::((j:ℚ)*s)::(r.2.map fun (i:Nat) => (i:ℚ)*s)
    let L := BoundaryChart.actual t.chart (ShapeRefs.join (t.corridor.coords args) (t.room.coords s))
    let J := GalleryBoundary.joined path out
    (mapPoly (shift (-door j)) (Polygon.mk (v.map ratPoint))).filled=L.filled∪shift (-door j) '' J.rest ∧
      IsClosed (shift (-door j) '' J.rest) ∧
      L.filled∩shift (-door j) '' J.rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) ((W (scale eqs):ℚ),1) ∧
      L.filled=shift (-door j) '' (RealizedDoors.wing e).filled := by
  intro s args L J
  let d := door j
  have hit : (drawOne t (scale eqs) j r.2).1=some e := by
    have h := path.2
    rwa [choose_get catalog (fun t => drawOne t (scale eqs) j r.2) r.1 (none,0) ht] at h
  have opened : atDoor d (W (scale eqs)) (t.chart.draw (ShapeRefs.join (t.corridor.coords args) (t.room.coords s)))=some e.2 := by
    simp only [drawOne] at hit
    obtain ⟨l,hl,el⟩ := Option.map_eq_some_iff.mp hit
    rw [←el]; exact hl
  obtain ⟨k,rot⟩ := placed opened
  have wingFilled : (RealizedDoors.wing e).filled=shift d '' L.filled := by
    change (Polygon.mk (e.2.map ratPoint)).filled=_
    rw [rot,Existence.filled_rotate,filled_mapPoly]; rfl
  have Lw : L.filled=shift (-d) '' (RealizedDoors.wing e).filled := by rw [wingFilled,unshift_image]
  refine ⟨?_,?_,?_,Lw⟩
  · rw [filled_mapPoly,J.fill,Set.image_union,wingFilled,unshift_image]
  · have : shift (-d) '' J.rest=shift d ⁻¹' J.rest := by
      ext p; constructor
      · rintro ⟨q,hq,rfl⟩; simpa [shift_cancel'] using hq
      · intro hp; exact ⟨shift d p,hp,shift_cancel d p⟩
    rw [this]; exact J.closed.preimage (shift_continuous d)
  · have inj : Function.Injective (shift (-d)) := (shift (-d)).injective
    rw [Lw,←Set.image_inter inj,J.contact,image_segment']
    congr 1 <;> rw [shift_pt] <;> ext <;> simp [d,BankCoordinates.door]

/-- The constants of the local test are the hub's constants. -/
theorem consts (n bank rank j : Nat) (hn : 0<n) :
    let sr : ℝ := ((1/n:ℚ):ℝ)
    (W n:ℝ)=sr/320 ∧ (D n:ℝ)=50050/sr^2 ∧
    (baseRate n bank rank j:ℝ)=((bank:ℝ)-1/5)/1001+5/2002*(((rank:ℚ)*(1/n:ℚ):ℚ):ℝ)+40/1001*(((j:ℚ)*(1/n:ℚ):ℚ):ℝ)*sr := by
  intro sr
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  refine ⟨?_,?_,?_⟩
  · simp only [sr,W]; push_cast; field_simp
  · simp only [sr,D,k]; push_cast; field_simp; ring
  · simp only [sr,baseRate,slotX,D,k,W,delta,door]; push_cast; field_simp; ring

/-- Translating a target of the gallery into the wing's frame. -/
theorem shift_target (d : ℚ) (c τ y W b D : ℝ) :
    shift (-d) (((d:ℝ)+c+(c-(W+b*D+τ))*(y-1)/D,y):Point)=(c+(c-(W+b*D+τ))*(y-1)/D,y) := by
  rw [shift_pt]; ext <;> simp; ring

/-- A guard blind to the gallery's copy targets is blind in the wing's frame. -/
theorem blind_shift {P : Polygon} {Wg : Polygon} {d : ℚ} {W b D : ℝ} {g : Point}
    (h : ∀ τ c y : ℝ, 0≤τ → τ≤3/2 → 0≤c → c≤W → 7/3≤y →
      (((d:ℝ)+c+(c-(W+b*D+τ))*(y-1)/D,y):Point)∈Wg.filled → ¬P.Sees g ((d:ℝ)+c+(c-(W+b*D+τ))*(y-1)/D,y)) :
    CopyRoles.Blind (mapPoly (shift (-d)) P) (shift (-d) '' Wg.filled) W b D (shift (-d) g) := by
  intro τ c y τ0 τ1 c0 c1 hy hz sees
  rw [←shift_target d c τ y W b D] at hz sees
  rw [ArtGallery.Vis.Cert.sees_mapPoly_iff] at sees
  have hz' : (((d:ℝ)+c+(c-(W+b*D+τ))*(y-1)/D,y):Point)∈Wg.filled := by
    obtain ⟨q,hq,e⟩ := hz
    have := (shift (-d)).injective e
    rwa [←this]
  exact h τ c y τ0 τ1 c0 c1 hy hz' sees

/-- The emitted records of a row are its template's index data on the grid. -/
theorem emitted_eq {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {i : Nat} {t : Template}
    (ht : catalog[r.1]?=some t) {idx : CorridorProgram.Data Nat} {arity : Nat} (rec : CopySpec.Records t idx arity)
    (size : r.2.length=arity) (hn : 65≤scale eqs) (hi : i≤scale eqs) (hr : ∀ k∈r.2,k≤scale eqs) :
    let s : ℚ := 1/(scale eqs)
    let args := s::((i:ℚ)*s)::(r.2.map fun (k:Nat) => (k:ℚ)*s)
    GlobalPins.emitted eqs r i=idx.2.map (fun l => l.map fun p =>
      ((IndexedWing.grid t args false).getD p.1 0,(IndexedWing.grid t args true).getD p.2 0)) := by
  intro s args
  unfold GlobalPins.emitted
  rw [choose_get catalog _ r.1 [] ht]
  exact rec size (scale eqs) i hn hi hr

/-- A spot of the row, moved back into the wing's frame, is the chart segment of its nodes. -/
theorem spot_local {X Y : List ℝ} {gx gy : List ℚ} (hX : X=gx.map (fun q : ℚ => (q:ℝ)))
    (hY : Y=gy.map (fun q : ℚ => (q:ℝ))) (d : ℚ) (l : List (Nat × Nat)) (hl : 2<l.length) :
    shift (-d) '' ArtGallery.segment
      (HighStep.moved d ((l.map fun p => (gx.getD p.1 0,gy.getD p.2 0)).getD 1 (0,0)))
      (HighStep.moved d ((l.map fun p => (gx.getD p.1 0,gy.getD p.2 0)).getD 2 (0,0)))=
    ArtGallery.segment (gridPt X Y (CellRoles.spotA l)) (gridPt X Y (CellRoles.spotB l)) := by
  rw [image_segment']
  have e (k : Nat) (hk : k<l.length) : shift (-d) (HighStep.moved d ((l.map fun p => (gx.getD p.1 0,gy.getD p.2 0)).getD k (0,0)))=
      gridPt X Y (l.getD k (0,0)) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hk),List.getElem_map,List.getD_eq_getElem _ _ hk]
    simp only [HighStep.moved,shift_pt,ratPoint,gridPt,hX,hY]
    have gx' : (gx.map (fun q : ℚ => (q:ℝ))).getD l[k].1 0=((gx.getD l[k].1 0:ℚ):ℝ) := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map]; cases gx[l[k].1]? <;> simp
    have gy' : (gy.map (fun q : ℚ => (q:ℝ))).getD l[k].2 0=((gy.getD l[k].2 0:ℚ):ℝ) := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map]; cases gy[l[k].2]? <;> simp
    rw [gx',gy']; ext <;> push_cast <;> ring
  rw [e 1 (by omega),e 2 hl]; rfl

/-- A boundary guard cover moves with the gallery. -/
theorem cover_shift {P : Polygon} {G : Finset Point} (hcov : P.IsGuardSetOnBoundary (G:Set Point)) (d : ℚ) :
    ∀ z∈(mapPoly (shift (-d)) P).filled, ∃ g∈G.image (shift (-d)), (mapPoly (shift (-d)) P).Sees g z := by
  intro z hz
  rw [filled_mapPoly] at hz
  obtain ⟨q,hq,rfl⟩ := hz
  obtain ⟨g,hg,sees⟩ := hcov.2 q hq
  exact ⟨shift (-d) g,Finset.mem_image_of_mem _ hg,(ArtGallery.Vis.Cert.sees_mapPoly_iff _ P g q).mpr sees⟩

end ArtGallery.Orthogonal.BoundaryPoint.CopyGlobal
end
