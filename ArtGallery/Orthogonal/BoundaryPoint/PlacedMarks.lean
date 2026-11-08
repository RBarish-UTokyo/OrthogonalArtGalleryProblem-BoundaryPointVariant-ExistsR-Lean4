module

public import ArtGallery.Orthogonal.BoundaryPoint.GalleryBoundary
public import ArtGallery.Orthogonal.BoundaryPoint.WingMarks

/-! # Transporting physical guard spots, intervals and witnesses into the full gallery -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PlacedMarks
open Set Geometry ChartDrawing RegisterTable RegisterOrder ShapeRefs MarginCert LinearRegister
open WingMarks WingEnvelope WingEnvelopeCert ContourJoin RectContour BankCoordinates

def separated (t : Template) (bs : List Box) (cache : List Entry) (e : (Ref × Ref) × (Ref × Ref)) : Bool :=
  let x := extent bs cache t.room.x
  let y := extent bs cache t.room.y
  decide ((x e.1.1).hi<0 ∧ (x e.2.1).hi<0) ||
  decide (1<(x e.1.1).lo ∧ 1<(x e.2.1).lo) ||
  decide (1<(y e.1.2).lo ∧ 1<(y e.2.2).lo)

def check (t : Template) (bs : List Box) (cache : List Entry) :=
  (requests (refs t).2).all (separated t bs cache)

def Away (t : Template) (args : List ℚ) : Prop :=
  let g := ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))
  ∀ e∈requests g.2,∀ q∈ArtGallery.segment (ratPoint e.1) (ratPoint e.2),q.1<0 ∨ 1<q.1 ∨ 1<q.2

private theorem bounded {args xs p bs cache} (m : Model args xs p bs cache) (a : RoomCoordinates.Axis) (r : Ref) :
    (extent bs cache a r).lo≤readRef xs a (getRat args 0) r ∧
      readRef xs a (getRat args 0) r≤(extent bs cache a r).hi := by
  cases r with
  | register i => exact m.bounds i
  | origin => exact ⟨le_refl _,le_refl _⟩
  | level i => rw [←formula m]; exact RegisterForm.form_bound (atom_bound m.bounds) m.pos.le m.upper _

theorem away {t : Template} {args xs rows bs cache} (m : Model args xs rows bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) (pass : check t bs cache=true) : Away t args := by
  let s := getRat args 0
  let g := ShapeRefs.join (t.corridor.coords args) (t.room.coords s)
  let pt (p : Ref × Ref) := (readRef xs t.room.x s p.1,readRef xs t.room.y s p.2)
  have roles : g.2=(refs t).2.map (List.map pt) := by
    rw [show g=ShapeRefs.join (t.corridor.coords args) (t.room.coords s) from rfl,←ShapeRefs.coords,←run]; rfl
  change ∀ e∈requests g.2,_
  intro req hReq q hq
  rw [roles,requests_map] at hReq
  obtain ⟨e,source,eq⟩ := List.mem_map.mp hReq
  subst req
  have bnd := List.all_eq_true.mp pass e source
  have hx (i) := bounded m t.room.x i
  have hy (i) := bounded m t.room.y i
  obtain ⟨u,hu,hU,rfl⟩ := mem_segment_iff_lerp.mp hq
  have X := HighStep.interpolated ((pt e.1).1:ℝ) ((pt e.2).1:ℝ) hu hU
  have Y := HighStep.interpolated ((pt e.1).2:ℝ) ((pt e.2).2:ℝ) hu hU
  change _<0 ∨ 1<_ ∨ 1<_
  simp only [separated,Bool.or_eq_true,decide_eq_true_eq] at bnd
  rcases bnd with (left|right)|above
  · left
    exact X.2.trans_lt (max_lt (by exact_mod_cast (hx e.1.1).2.trans_lt left.1)
      (by exact_mod_cast (hx e.2.1).2.trans_lt left.2))
  · right; left
    exact (lt_min (by exact_mod_cast right.1.trans_le (hx e.1.1).1)
      (by exact_mod_cast right.2.trans_le (hx e.2.1).1)).trans_le X.1
  · right; right
    exact (lt_min (by exact_mod_cast above.1.trans_le (hy e.1.2).1)
      (by exact_mod_cast above.2.trans_le (hy e.2.2).1)).trans_le Y.1

theorem away_at_size {t : Template} {rs : List Nat} (basic : Cert t rs.length) (n j : Nat)
    (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n) (cache : List Entry)
    (tables : let p := t.corridor.baseRows++t.corridor.rest
      cache.length=p.reverse.length ∧ Verified p.reverse (stack [] p) cache 0 p.reverse.length ∧ check t (stack [] p) cache=true) :
    let s := (1:ℚ)/n
    Away t (s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)) := by
  let s := (1:ℚ)/n
  let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
  let p := t.corridor.baseRows++t.corridor.rest
  let xs := execRat args [] p
  have pos : 0<getRat args 0 := by change 0<(1:ℚ)/n; positivity
  have small : getRat args 0≤RegisterForm.cap := by
    change (1:ℚ)/n≤1/65
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
  have run : Ledger args p.reverse xs := by simpa only [List.append_nil,xs] using exec_ledger (Ledger.nil (args:=args)) p
  have bounds := lookup_bound (xs:=[]) (parameters n j rs hn hj hr) (by exact empty_encloses) basic.arithmetic
  obtain ⟨size,valid,clear⟩ := tables
  have m : Model args xs p.reverse (stack [] p) cache := ⟨run,bounds,pos,small,RegisterTable.model run bounds pos small size valid⟩
  exact away m rfl clear

def move (d : ℚ) (p : Point) : Point := (p.1+(d:ℝ),p.2)

theorem move_boundary {l path : List Vertex} {d w : ℚ} (out : atDoor d w l=some path) {p : Point}
    (hp : p∈(Polygon.mk (l.map ratPoint)).boundary) : move d p∈(Polygon.mk (path.map ratPoint)).boundary := by
  let A : Point ≃ᵃ[ℝ] Point := AffineEquiv.constVAdd ℝ Point ((d:ℝ),0)
  have action (q : Point) : A q=move d q := by
    change ((d:ℝ)+q.1,0+q.2)=(q.1+d,q.2); simp [add_comm]
  have f : (A ∘ ratPoint)=HighStep.moved d := by
    funext v; simp [Function.comp_def,action,move,HighStep.moved,ratPoint]
  have imagePoint : move d p∈(Hardening.Invariance.mapPoly A ⟨l.map ratPoint⟩).boundary := by
    rw [Hardening.Invariance.boundary_mapPoly]
    exact ⟨p,hp,action p⟩
  change move d p∈(Polygon.mk ((l.map ratPoint).map A)).boundary at imagePoint
  rw [List.map_map,f] at imagePoint
  let i := l.idxOf (0,1)
  unfold atDoor at out; dsimp only at out
  split at out
  · contradiction
  next good =>
    have bound : i+1≤l.length := by
      have h : ¬(i≥l.length ∨ (l.getD ((i+1)%l.length) (0,0) != (w,1))=true) := by
        simpa only [i,Bool.or_eq_true,decide_eq_true_eq] using good
      omega
    obtain rfl := Option.some.inj out
    change _∈(Polygon.mk (((l.drop (i+1)++l.take (i+1)).map _).map ratPoint)).boundary
    rw [←List.rotate_eq_drop_append_take bound,List.map_map]
    change _∈(Polygon.mk ((l.rotate (i+1)).map (HighStep.moved d))).boundary
    rw [List.map_rotate,←InsideDoor.rotate_list,Existence.boundary_rotate]
    exact imagePoint

theorem in_gallery {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {vs g}
    (path : WingSeparation.emitted eqs r j e) (out : CandidateWord.vertices eqs=some (vs,g))
    {l : List Vertex} (opened : atDoor (door j) (W (CompiledSize.scale eqs)) l=some e.2) {p : Point}
    (hp : p∈(Polygon.mk (l.map ratPoint)).boundary) (away : p.1<0 ∨ 1<p.1 ∨ 1<p.2) :
    move (door j) p∈(Polygon.mk (vs.map ratPoint)).boundary := by
  have moved := move_boundary opened hp
  have ne : eqs≠[] := by intro z; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  have weak : (W (CompiledSize.scale eqs):ℝ)≤1/2 := by
    rw [cast_W]; apply BankPitch.width_le_half; exact_mod_cast (show 1≤CompiledSize.scale eqs by have := (CompiledSize.scale_bounds ne).1; omega)
  apply (GalleryBoundary.wing_iff path out (Jordan.boundary_subset_filled _ moved) ?_).mpr moved
  rintro ⟨t,ht,hu,ev⟩
  have X := congrArg Prod.fst ev
  have Y := congrArg Prod.snd ev
  simp only [move,sub_self,mul_zero,add_zero,add_sub_cancel_left] at X Y
  rcases away with left|right|up
  · linarith [mul_nonneg ht (show 0≤(W (CompiledSize.scale eqs):ℝ) by unfold W; positivity)]
  · have pos : 0≤(W (CompiledSize.scale eqs):ℝ) := by unfold W; positivity
    linarith [mul_le_mul_of_nonneg_right hu pos]
  · linarith

end ArtGallery.Orthogonal.BoundaryPoint.PlacedMarks
end
