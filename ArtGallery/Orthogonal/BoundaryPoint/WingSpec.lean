module

public import ArtGallery.Orthogonal.BoundaryPoint.CopySpec
public import ArtGallery.Orthogonal.BoundaryPoint.CatalogRanks
public import ArtGallery.Orthogonal.BoundaryPoint.ValueChain

/-! # The cover of one wing in its local frame

`Cover t idx tag mv` says: at every admissible size, in any polygon containing the
filled chart, if the copy channels carry parameters `τ c ∈ [0, 3/2]` whose values
`τ c + 1/2` satisfy the row relation of `tag`, and every base guard on the floor sees
the door segment, then every filled point of the chart is seen by the guard of a role
(a stationary role at its record point, a moving role `r` with entry `(r, c, a, b)` of
`mv` on its spot `[a, b]` at the parameter of channel `c`) or by a base guard. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingSpec
open ChartDrawing BoundaryChart IndexedWing MarginCert SepCert CellRoles RoomGrid CorridorProgram GridAtom
open ArtGallery.Orthogonal.Hard

/-- The guard of role `r`: a moving role on its spot at the parameter of its channel, any other
role at its record point. -/
noncomputable def guardOf (X Y : List ℝ) (mv : List (Nat × Nat × Index × Index)) (τ : Nat → ℝ)
    (roles : List (List Index)) (r : Nat) : Point :=
  match mv.lookup r with
  | some m => CopyLower.receiver X Y m.2.1 m.2.2 (τ m.1)
  | none => gridPt X Y ((roles.getD r []).getD 0 (0,0))

/-- The base guard of channel `c` on the floor below the door. -/
noncomputable def base (tag : Nat) (args : List ℚ) (τ : Nat → ℝ) (c : Nat) : Point :=
  let sr : ℝ := getRat args 0
  let D : ℝ := 50050/sr^2
  let b : ℝ := ((((CatalogRanks.profileBanks tag).getD c 0:Nat):ℝ)-1/5)/1001+
    5/2002*(getRat args (c+2):ℝ)+40/1001*(getRat args 1:ℝ)*sr
  (sr/320+b*D+τ c,1-D)

def Cover (t : Template) (idx : Data Nat) (tag : Nat) (mv : List (Nat × Nat × Index × Index)) : Prop :=
  ∀ {rs : List Nat}, rs.length=(CatalogRanks.profileBanks tag).length → ∀ n j : Nat, 65≤n → j≤n → (∀ i∈rs,i≤n) →
    let s : ℚ := 1/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    let X := (grid t args false).map (fun q : ℚ => (q:ℝ))
    let Y := (grid t args true).map (fun q : ℚ => (q:ℝ))
    let W : ℝ := (s:ℝ)/320
    let L := (actual t.chart (ShapeRefs.join (t.corridor.coords args) (t.room.coords s))).filled
    ∀ {P : Polygon}, L⊆P.filled → ∀ τ : Nat → ℝ, (∀ c<(CatalogRanks.profileBanks tag).length, 0≤τ c ∧ τ c≤3/2) →
    CatalogLogic.relation tag ((List.range (CatalogRanks.profileBanks tag).length).map fun c => τ c+1/2) →
    (∀ c<(CatalogRanks.profileBanks tag).length, ∀ d∈ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1),
      P.Sees (base tag args τ c) d) →
    ∀ z∈L, (∃ r, r < idx.2.length ∧ P.Sees (guardOf X Y mv τ idx.2 r) z) ∨
      ∃ c, c < (CatalogRanks.profileBanks tag).length ∧ P.Sees (base tag args τ c) z

/-- A catalogue entry: the index data of a template with its moving roles, the wing cover, the
emitted records, six-entry role records, and the spots of the moving roles. -/
def Entry (t : Template) (tag : Nat) (mv : List (Nat × Nat × Index × Index)) : Prop :=
  ∃ idx : Data Nat, Cover t idx tag mv ∧ CopySpec.Records t idx (CatalogRanks.profileBanks tag).length ∧
    (∀ l∈idx.2, l.length=6) ∧
    ∀ m∈mv, m.1 < idx.2.length ∧ CellRoles.spotA (idx.2.getD m.1 [])=m.2.2.1 ∧
      CellRoles.spotB (idx.2.getD m.1 [])=m.2.2.2 ∧ m.2.2.2.2=m.2.2.1.2 ∧
      m.2.1<(CatalogRanks.profileBanks tag).length

/-- The base slope of a copy channel is at most the receiver slope: both central rays meet the nook
axis at the same point, and the door lies left of the window corner. -/
theorem slope_le {W b H cx r : ℝ} (inc : W-b*H=cx-r*H) (hH : 0<H) (hW : W≤cx) : b≤r := by
  by_contra h
  push Not at h
  nlinarith [mul_pos (sub_pos.2 h) hH]

/-- On a horizontal room role, the copy receiver at parameter `τ` is the room guard at `τ`. -/
theorem receiver_slot {t : Template} {idx : Data Nat} {arity : Nat} (rec : CopySpec.Records t idx arity)
    {rs : List Nat} (size : rs.length=arity) {n j : Nat} (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n)
    {m : Nat} (hm : m<t.room.roles.length) (h6 : 2<(t.room.roles[m]).length)
    (hi : t.corridor.roles.length+m < idx.2.length) {ra rb : Index}
    (hra : CellRoles.spotA (idx.2[t.corridor.roles.length+m])=ra)
    (hrb : CellRoles.spotB (idx.2[t.corridor.roles.length+m])=rb) (hy : rb.2=ra.2) (τ : ℝ) :
    let s : ℚ := 1/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    CopyLower.receiver ((grid t args false).map (fun q : ℚ => (q:ℝ))) ((grid t args true).map (fun q : ℚ => (q:ℝ)))
      ra rb τ=SlotLines.slot (gridPt (t.room.x.coordsR ((s:ℚ):ℝ)) (t.room.y.coordsR ((s:ℚ):ℝ))) t.room.roles m τ := by
  intro s args
  obtain ⟨i1,e1⟩ := ValueChain.room_node rec size hn hj hr hm (q:=1) (by omega)
  obtain ⟨i2,e2⟩ := ValueChain.room_node rec size hn hj hr hm (q:=2) h6
  have cast (xs : List ℚ) (a : Nat) : (xs.map (fun q : ℚ => (q:ℝ))).getD a 0=((xs.getD a 0:ℚ):ℝ) := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]; cases xs[a]? <;> simp
  have cx : t.room.x.coordsR ((s:ℚ):ℝ)=(t.room.x.coordsQ s).map (fun q : ℚ => (q:ℝ)) := by
    rw [RoomCoordinates.cast_coords]
  have cy : t.room.y.coordsR ((s:ℚ):ℝ)=(t.room.y.coordsQ s).map (fun q : ℚ => (q:ℝ)) := by
    rw [RoomCoordinates.cast_coords]
  subst hra hrb
  have ex1 := congrArg (fun q : ℚ => (q:ℝ)) (congrArg Prod.fst e1)
  have ey1 := congrArg (fun q : ℚ => (q:ℝ)) (congrArg Prod.snd e1)
  have ex2 := congrArg (fun q : ℚ => (q:ℝ)) (congrArg Prod.fst e2)
  have ey2 := congrArg (fun q : ℚ => (q:ℝ)) (congrArg Prod.snd e2)
  simp only at ex1 ey1 ex2 ey2
  simp only [CellRoles.spotA,CellRoles.spotB] at hy
  simp only [CopyLower.receiver,SlotLines.slot,gridPt,CellRoles.spotA,CellRoles.spotB,cast,cx,cy,
    List.getD_eq_getElem _ _ hm]
  have hyR : (((t.room.y.coordsQ s).getD ((t.room.roles[m]).getD 2 (0,0)).2 0 : ℚ) : ℝ)=
      (((t.room.y.coordsQ s).getD ((t.room.roles[m]).getD 1 (0,0)).2 0 : ℚ) : ℝ) := by
    rw [← ey2,hy,ey1]
  rw [ex1,ey1,ex2,hyR]
  simp only [Geometry.lerp,sub_self,mul_zero,add_zero]
  ext <;> simp only <;> ring

end ArtGallery.Orthogonal.BoundaryPoint.WingSpec
end
