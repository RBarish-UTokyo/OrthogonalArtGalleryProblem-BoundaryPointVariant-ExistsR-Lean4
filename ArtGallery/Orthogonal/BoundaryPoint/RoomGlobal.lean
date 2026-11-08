module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyMain
public import ArtGallery.Orthogonal.BoundaryPoint.RoomWedge
public import ArtGallery.Orthogonal.BoundaryPoint.RoomExclusion
public import ArtGallery.Orthogonal.BoundaryPoint.SlotLines

/-! # A joined room in the emitted gallery

In the local frame of a row's wing, the emitted polygon is the union of the staircase cells,
the room and the translated rest of the gallery. The room is attached through its window and
the wing through its door, giving the attachment tree of the room. Every guard that does not
own a room role is blind to a critical box of the room: hub guards and guards of other rows lie
in the rest and cross the door, the corridor guards of the row lie in certified register boxes
away from the window wedge. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomGlobal
open Set ChartDrawing ContourJoin RectContour BankCoordinates CompiledSize PinTransport Hardening.Invariance
open CatalogPlan HubOwners HubRoles CopyGlobal ArtGallery.Orthogonal.Hard RoomWedge MarginCert CorridorProgram

theorem tiles_closed (rs : List (Rect ℚ)) : IsClosed (WingTiles.cells rs) := by
  have e : WingTiles.cells rs=⋃ r∈{r | r∈rs}, {q : Point | (r.1:ℝ)≤q.1 ∧ q.1≤(r.2.1:ℝ) ∧
      (r.2.2.1:ℝ)≤q.2 ∧ q.2≤(r.2.2.2:ℝ)} := by
    ext q; simp only [WingTiles.cells,Set.mem_iUnion,Set.mem_setOf_eq,exists_prop]
  rw [e]
  refine (List.finite_toSet rs).isClosed_biUnion (fun r _ => ?_)
  exact (isClosed_le continuous_const continuous_fst).inter ((isClosed_le continuous_fst continuous_const).inter
    ((isClosed_le continuous_const continuous_snd).inter (isClosed_le continuous_snd continuous_const)))

/-- The box of a register node `(x register, y register)`. -/
def nodeBox (bs : List Box) (p : Nat × Nat) : QBox :=
  ((getBox bs p.1).lo,(getBox bs p.1).hi,(getBox bs p.2).lo,(getBox bs p.2).hi)

/-- The register box of the spot of a corridor role. -/
def spotBox (l : Layout) (r : List (Nat × Nat)) : QBox :=
  let bs := stack [] (l.baseRows++l.rest)
  hull (nodeBox bs (r.getD 1 (0,0))) (nodeBox bs (r.getD 2 (0,0)))

/-- Every corridor spot misses the window wedge of a target box and lies left of the room. -/
def corridorClear (l : Layout) (win zb : QBox) (xmin : ℚ) : Bool :=
  l.roles.all fun r => sep (spotBox l r) win zb && decide ((spotBox l r).2.1<xmin)

/-- The standard parameter boxes of a corridor program. -/
def params (arity : Nat) : List Box := ⟨0,1/65⟩::⟨0,1⟩::List.replicate arity ⟨0,1⟩

theorem args_enclose {n j : Nat} (hn : 65≤n) (hj : j≤n) {rs : List Nat} (hr : ∀ k∈rs,k≤n) :
    let s : ℚ := 1/n
    Encloses (params rs.length) ((s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)).map (fun q : ℚ => (q:ℝ))) := by
  intro s
  have unit {k : Nat} (hk : k≤n) : Box.Mem ⟨0,1⟩ (((k:ℚ)*s:ℚ):ℝ) := by
    have h := MarginCert.normalized_index hn hk
    simpa [s,div_eq_mul_inv] using h
  have tail : ∀ rs : List Nat, (∀ k∈rs,k≤n) →
      Encloses (List.replicate rs.length ⟨0,1⟩) ((rs.map fun (i:Nat) => (i:ℚ)*s).map (fun q : ℚ => (q:ℝ))) := by
    intro rs hr
    induction rs with
    | nil => intro i; simp [getBox,getReal,zeroBox,Box.Mem]
    | cons k rs ih =>
      simp only [List.length_cons,List.replicate_succ,List.map_cons]
      exact Encloses.cons (unit (hr k (by simp))) (ih (fun k hk => hr k (by simp [hk])))
  simp only [params,List.map_cons]
  refine Encloses.cons ?_ (Encloses.cons (unit hj) (tail rs hr))
  have h := MarginCert.reciprocal_size hn
  simpa [s] using h

section Main
variable {eqs : List ETRINV.Constraint} {v : List Vertex} {gN : Nat}
variable (ne : eqs≠[]) (out : CandidateWord.vertices eqs=some (v,gN))
include ne out

local notation "PP" => Polygon.mk (v.map ratPoint)

/-- The joined frame of a room: the global frame of `Frame` and the attachment tree. -/
theorem frame (i : Fin (PrivateRoles.rows eqs).length) {t : Template}
    (ht : catalog[((PrivateRoles.rows eqs)[i]).1]?=some t) {C R : Set Point}
    (split : let s : ℚ := 1/(scale eqs)
      let args := s::(((i:Nat):ℚ)*s)::(((PrivateRoles.rows eqs)[i]).2.map fun (k:Nat) => (k:ℚ)*s)
      (BoundaryChart.actual t.chart (ShapeRefs.join (t.corridor.coords args) (t.room.coords s))).filled=C∪R)
    (hC : IsClosed C) (hR : IsClosed R) {A B : Point} (hwin : C∩R=ArtGallery.segment A B)
    {ba bb : QBox} (hA : ba.Mem A) (hB : bb.Mem B) {xmin : ℚ} (roomX : ∀ p∈R, (xmin:ℝ)≤p.1)
    (doorX : (1/20800:ℚ)<xmin) :
    Frame (mapPoly (shift (-(door (i:Nat)))) PP) C R
        (shift (-(door (i:Nat))) '' (GalleryBoundary.joined (PrivateRoles.entrance_spec eqs i) out).rest)
        (hull ba bb) (0,1/20800,1,1) xmin ∧
      WindowTree.Attachments R (mapPoly (shift (-(door (i:Nat)))) PP).filled := by
  obtain ⟨fill,closed,contact,-⟩ := frame2 (PrivateRoles.entrance_spec eqs i) out ht
  simp only at split
  rw [split] at fill contact
  refine ⟨⟨fill,hC,hR,closed,?_,?_,roomX,doorX⟩,?_⟩
  · rw [hwin]; exact hull_mem hA hB
  · rw [contact]
    rintro p ⟨t,t0,t1,rfl⟩
    simp only [QBox.Mem]
    have hW : (0:ℝ)≤(W (scale eqs):ℝ) ∧ (W (scale eqs):ℝ)≤1/20800 := by
      have hn : (65:ℝ)≤scale eqs := by exact_mod_cast (scale_bounds ne).1
      unfold W; push_cast
      exact ⟨by positivity,by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith⟩
    push_cast
    refine ⟨by nlinarith,by nlinarith,by linarith,by linarith⟩
  · have t1 : WindowTree.Attachments R (R∪C) :=
      WindowTree.Attachments.attach (.start hR) hC (by rw [inter_comm,hwin]; exact Geometry.segment_convex A B)
    have t2 := WindowTree.Attachments.attach t1 closed
      (by rw [union_comm R C,contact]; exact Geometry.segment_convex _ _)
    rw [fill,union_comm C R]; exact t2

omit out in
/-- The corridor role spots of a row, in its frame. -/
theorem corridor_spot (ancs : List (List Nat)) (i : Fin (PrivateRoles.rows eqs).length) {t : Template}
    (ht : catalog[((PrivateRoles.rows eqs)[i]).1]?=some t)
    (hok : ok (params ((PrivateRoles.rows eqs)[i]).2.length) [] (t.corridor.baseRows++t.corridor.rest)=true)
    (k : Fin (PrivateRoles.records eqs i).length) (hk : (k:Nat)<t.corridor.roles.length) :
    ∀ g∈(PrivateRoles.group eqs ancs).spot ⟨i,k⟩, (spotBox t.corridor t.corridor.roles[(k:Nat)]).Mem (shift (-(door (i:Nat))) g) := by
  set n := scale eqs
  have hn : 65≤n := (scale_bounds ne).1
  have path := PrivateRoles.entrance_spec eqs i
  have rmem : (PrivateRoles.rows eqs)[i]∈(compile eqs).1 := List.getElem_mem _
  have hiN : (i:Nat)≤n := (CompiledAddresses.program_door eqs path.1).le
  have hrk : ∀ k∈((PrivateRoles.rows eqs)[i]).2,k≤n := fun k hk => (CompiledAddresses.program_ranks eqs rmem hk).le
  set s : ℚ := 1/n
  set args := s::(((i:Nat):ℚ)*s)::(((PrivateRoles.rows eqs)[i]).2.map fun (k:Nat) => (k:ℚ)*s)
  set xs := execRat args (execRat args [] t.corridor.baseRows) t.corridor.rest
  set f : Nat × Nat → Vertex := fun j => (getRat xs j.1,getRat xs j.2)
  set l := t.corridor.roles[(k:Nat)]
  have hR : PrivateRoles.records eqs i=(t.corridor.coords args).2++(t.room.coords s).2 := by
    simp only [PrivateRoles.records,GlobalPins.emitted]
    rw [choose_get catalog _ _ [] ht]; rfl
  have hrec : PrivateRoles.record eqs ⟨i,k⟩=l.map f := by
    simp only [PrivateRoles.record]
    rw [Fin.getElem_fin,List.getElem_of_eq hR,List.getElem_append_left (by simpa [Layout.coords] using hk)]
    simp [Layout.coords,readRole,l,f,xs]
  have six := PrivateRoles.record_six eqs ⟨i,k⟩
  rw [hrec,List.length_map] at six
  have hv := args_enclose hn hiN hrk
  have node (j : Nat) (hj : j<6) : (nodeBox (stack [] (t.corridor.baseRows++t.corridor.rest)) (l.getD j (0,0))).Mem
      (shift (-(door (i:Nat))) (HighStep.moved (door (i:Nat)) ((l.map f).getD j (0,0)))) := by
    have hj' : j<l.length := by rw [six]; exact hj
    rw [List.getD_eq_getElem (l.map f) _ (by simpa using hj'),List.getElem_map,List.getD_eq_getElem l _ hj']
    have bx := register_box hv hok l[j].1
    have by' := register_box hv hok l[j].2
    rw [←execRat_append] at bx by'
    simp only [nodeBox,QBox.Mem,HighStep.moved,shift_pt,ratPoint,f]
    push_cast
    refine ⟨?_,?_,?_,?_⟩
    · have := bx.1; simp only [xs] at *; linarith
    · have := bx.2; simp only [xs] at *; linarith
    · exact by'.1
    · exact by'.2
  intro g hg
  simp only [PrivateRoles.group,hrec] at hg
  have := Set.mem_image_of_mem (shift (-(door (i:Nat)))) hg
  rw [image_segment'] at this
  exact hull_mem (node 1 (by norm_num)) (node 2 (by norm_num)) _ this

omit ne out in
theorem records_length (i : Fin (PrivateRoles.rows eqs).length) {t : Template}
    (ht : catalog[((PrivateRoles.rows eqs)[i]).1]?=some t) :
    (PrivateRoles.records eqs i).length=t.corridor.roles.length+t.room.roles.length := by
  simp only [PrivateRoles.records,GlobalPins.emitted]
  rw [choose_get catalog _ _ [] ht]
  simp [GlobalPins.records,Layout.coords,PlanGeometry.ArithmeticRoom.coords]

omit ne out in
/-- The spot of a room role of a row, in its frame: the room's own role segment. -/
theorem room_spot (ancs : List (List Nat)) (i : Fin (PrivateRoles.rows eqs).length) {t : Template}
    (ht : catalog[((PrivateRoles.rows eqs)[i]).1]?=some t)
    (k : Fin (PrivateRoles.records eqs i).length) {m : Nat} (hm : (k:Nat)=t.corridor.roles.length+m)
    (hm' : m<t.room.roles.length) :
    let pt := gridPt (t.room.x.coordsR (1/(scale eqs:ℝ))) (t.room.y.coordsR (1/(scale eqs:ℝ)))
    shift (-(door (i:Nat))) '' (PrivateRoles.group eqs ancs).spot ⟨i,k⟩=
      ArtGallery.segment (pt (RoomExclusion.nodeAt t.room.roles m 1)) (pt (RoomExclusion.nodeAt t.room.roles m 2)) := by
  intro pt
  set s : ℚ := 1/(scale eqs)
  set args := s::(((i:Nat):ℚ)*s)::(((PrivateRoles.rows eqs)[i]).2.map fun (k:Nat) => (k:ℚ)*s)
  set l := t.room.roles[m]
  set f : Nat × Nat → Vertex := fun j => ((t.room.x.coordsQ s).getD j.1 0,(t.room.y.coordsQ s).getD j.2 0)
  have hR : PrivateRoles.records eqs i=(t.corridor.coords args).2++(t.room.coords s).2 := by
    simp only [PrivateRoles.records,GlobalPins.emitted]
    rw [choose_get catalog _ _ [] ht]; rfl
  have hc : (t.corridor.coords args).2.length=t.corridor.roles.length := by simp [Layout.coords]
  have hrec : PrivateRoles.record eqs ⟨i,k⟩=l.map f := by
    simp only [PrivateRoles.record]
    rw [Fin.getElem_fin,List.getElem_of_eq hR,List.getElem_append_right (by omega)]
    simp only [PlanGeometry.ArithmeticRoom.coords,List.getElem_map]
    congr 1
    · simp only [hc,hm,Nat.add_sub_cancel_left]; rfl
  have six := PrivateRoles.record_six eqs ⟨i,k⟩
  rw [hrec,List.length_map] at six
  have hs : ((s:ℚ):ℝ)=1/(scale eqs:ℝ) := by simp [s]
  have node (j : Nat) (hj : j<6) : shift (-(door (i:Nat))) (HighStep.moved (door (i:Nat)) ((l.map f).getD j (0,0)))=
      pt (RoomExclusion.nodeAt t.room.roles m j) := by
    have hj' : j<l.length := by rw [six]; exact hj
    rw [List.getD_eq_getElem (l.map f) _ (by simpa using hj'),List.getElem_map]
    have e1 : (1/(scale eqs:ℝ))=((s:ℚ):ℝ) := by simp [s]
    have cx : t.room.x.coordsR (1/(scale eqs:ℝ))=(t.room.x.coordsQ s).map (fun q : ℚ => (q:ℝ)) := by
      rw [e1,RoomCoordinates.cast_coords]
    have cy : t.room.y.coordsR (1/(scale eqs:ℝ))=(t.room.y.coordsQ s).map (fun q : ℚ => (q:ℝ)) := by
      rw [e1,RoomCoordinates.cast_coords]
    have gx (xs : List ℚ) (a : Nat) : (xs.map (fun q : ℚ => (q:ℝ))).getD a 0=((xs.getD a 0:ℚ):ℝ) := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map]; cases xs[a]? <;> simp
    simp only [RoomExclusion.nodeAt,List.getD_eq_getElem _ _ hm']
    rw [List.getD_eq_getElem t.room.roles[m] _ hj']
    simp only [HighStep.moved,shift_pt,ratPoint,f,pt,gridPt,cx,cy,gx]
    ext <;> push_cast <;> ring
  simp only [PrivateRoles.group,hrec]
  rw [image_segment',node 1 (by norm_num),node 2 (by norm_num)]

omit ne out in
/-- A point of a room role segment is the slot guard of a parameter in `[0,3/2]`. -/
theorem slot_of_mem {pt : RoomGrid.Index → Point} {roles : List (List RoomGrid.Index)} {m : Nat} {g : Point}
    (hg : g∈ArtGallery.segment (pt (RoomExclusion.nodeAt roles m 1)) (pt (RoomExclusion.nodeAt roles m 2))) :
    ∃ τ : ℝ, (0≤τ ∧ τ≤3/2) ∧ g=SlotLines.slot pt roles m τ := by
  obtain ⟨u,u0,u1,rfl⟩ := hg
  refine ⟨3/2*u,⟨by linarith,by linarith⟩,?_⟩
  simp only [SlotLines.slot,RoomExclusion.nodeAt,Geometry.lerp]
  ext <;> simp only <;> ring

/-- Every guard either owns a room role of the row or is blind to a room point in a box whose
window wedge the door and every corridor spot miss. -/
theorem classify (ancs : List (List Nat)) (G : Finset Point) (hcov : (PP).IsGuardSetOnBoundary (G:Set Point))
    (hevery : ∀ p∈G, ∃ ρ : HubRole eqs ⊕ PrivateRoles.Role eqs,
      (PP).Sees p (Sum.elim (HubOwners.group eqs PP).mark (PrivateRoles.group eqs ancs).mark ρ) ∧
      p∈Sum.elim (HubOwners.group eqs PP).spot (PrivateRoles.group eqs ancs).spot ρ)
    (i : Fin (PrivateRoles.rows eqs).length) {t : Template}
    (ht : catalog[((PrivateRoles.rows eqs)[i]).1]?=some t)
    (hok : ok (params ((PrivateRoles.rows eqs)[i]).2.length) [] (t.corridor.baseRows++t.corridor.rest)=true)
    {C R : Set Point} {win : QBox} {xmin : ℚ}
    (F : Frame (mapPoly (shift (-(door (i:Nat)))) PP) C R
        (shift (-(door (i:Nat))) '' (GalleryBoundary.joined (PrivateRoles.entrance_spec eqs i) out).rest)
        win (0,1/20800,1,1) xmin)
    {zb : QBox} (hdoor : sep (0,1/20800,1,1) win zb=true)
    (hclear : corridorClear t.corridor win zb xmin=true) {z : Point} (hz : z∈R) (hzb : zb.Mem z) :
    ∀ g∈G, ¬(mapPoly (shift (-(door (i:Nat)))) PP).Sees (shift (-(door (i:Nat))) g) z ∨
      ∃ k : Fin (PrivateRoles.records eqs i).length, t.corridor.roles.length≤(k:Nat) ∧
        (PP).Sees g ((PrivateRoles.group eqs ancs).mark ⟨i,k⟩) ∧ g∈(PrivateRoles.group eqs ancs).spot ⟨i,k⟩ := by
  intro g hg
  set d := door (i:Nat)
  have path := PrivateRoles.entrance_spec eqs i
  let J := GalleryBoundary.joined path out
  have gB : g∈(PP).boundary := hcov.1 hg
  have gF : g∈(PP).filled := Jordan.boundary_subset_filled _ gB
  -- a guard of the rest crosses the door
  have fromRest (h : g∈J.rest) : ¬(mapPoly (shift (-d)) PP).Sees (shift (-d) g) z :=
    F.from_rest (Set.mem_image_of_mem _ h) hz hzb hdoor
  obtain ⟨ρ,hsees,hspot⟩ := hevery g hg
  rcases ρ with h|x
  · -- a hub role: its guard is not in any wing
    left
    apply fromRest
    have hub : g∈(RealizedDoors.hub eqs).filled := by
      rcases split_filled ne out gF with hh|hw
      · exact hh
      · exfalso
        apply HubOwners.wing_free ne out (i:=h) (t:=tipL eqs h) (Or.inl rfl) hw
        have : (PP).Sees g (tipL eqs h) := by simpa [JoinedBudget.Group.mark,HubOwners.group] using hsees
        exact Vis.sees_comm.mp this
    exact GlobalBlind.hub_rest ne out path hub
  · by_cases hx : x.1=i
    · obtain ⟨xi,xk⟩ := x
      simp only at hx
      subst hx
      by_cases hk : t.corridor.roles.length≤(xk:Nat)
      · exact Or.inr ⟨xk,hk,hsees,hspot⟩
      · -- a corridor role of the row
        left
        replace hk := not_le.mp hk
        have box := corridor_spot ne ancs xi ht hok xk hk g hspot
        have cl := List.all_eq_true.mp hclear _ (List.getElem_mem hk)
        simp only [Bool.and_eq_true,decide_eq_true_eq] at cl
        apply F.through _ _ box hz hzb cl.1
        · rw [filled_mapPoly]; exact Set.mem_image_of_mem _ gF
        · intro hR
          have := F.roomX _ hR
          have := box.2.1
          have := (Rat.cast_lt (K:=ℝ)).mpr cl.2
          linarith
    · -- a role of another row: its guard lies in another wing
      left
      apply fromRest
      have hw := CopyMain.spot_wing ancs x hspot
      have hii : ((x.1:Nat))≠(i:Nat) := fun h => hx (Fin.ext h)
      have gJ := gF
      rw [J.fill] at gJ
      rcases gJ with hin|hr
      · exfalso
        exact Set.disjoint_left.mp (WingSeparation.disjoint path (PrivateRoles.entrance_spec eqs x.1) hii.symm) hin hw
      · exact hr

end Main

end ArtGallery.Orthogonal.BoundaryPoint.RoomGlobal
end
