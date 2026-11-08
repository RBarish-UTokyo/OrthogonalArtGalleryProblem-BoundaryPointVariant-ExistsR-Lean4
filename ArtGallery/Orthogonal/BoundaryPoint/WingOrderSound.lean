module

public import ArtGallery.Orthogonal.BoundaryPoint.RegisterOrder
public import ArtGallery.Orthogonal.BoundaryPoint.HighStep
public import ArtGallery.Invariance.Affine

/-! # Realized staircase simplicity from the checked mixed-grid orders -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingOrderSound
open RegisterOrder RegisterTable MarginCert RegisterForm LinearRegister ChartDrawing
open WingEnvelopeCert BoundaryChart BankCoordinates ContourJoin RectContour

theorem simple_at_door {l path : List Vertex} {d w : ℚ} (h : (Polygon.mk (l.map ratPoint)).Simple)
    (out : atDoor d w l=some path) : (Polygon.mk (path.map ratPoint)).Simple := by
  let A : Point ≃ᵃ[ℝ] Point := AffineEquiv.constVAdd ℝ Point ((d:ℝ),0)
  have action (p : Vertex) : A (ratPoint p)=HighStep.moved d p := by
    change ((d:ℝ)+(p.1:ℝ),0+(p.2:ℝ))=_
    simp [HighStep.moved,ratPoint,add_comm]
  have translated := Hardening.Invariance.simple_mapPoly A _ h
  change (Polygon.mk ((l.map ratPoint).map A)).Simple at translated
  rw [List.map_map] at translated
  have f : (A ∘ ratPoint)=HighStep.moved d := funext action
  rw [f] at translated
  let i := l.idxOf (0,1)
  unfold atDoor at out
  dsimp only at out
  split at out
  · contradiction
  next good =>
    have bounded : i+1≤l.length := by
      have h : ¬(i≥l.length ∨ (l.getD ((i+1)%l.length) (0,0) != (w,1))=true) := by
        simpa only [i,Bool.or_eq_true,decide_eq_true_eq] using good
      omega
    obtain rfl := Option.some.inj out
    change (Polygon.mk (((l.drop (i+1)++l.take (i+1)).map _).map ratPoint)).Simple
    rw [←List.rotate_eq_drop_append_take bounded,List.map_map]
    change (Polygon.mk ((l.rotate (i+1)).map (HighStep.moved d))).Simple
    rw [List.map_rotate,←InsideDoor.rotate_list]
    exact Existence.simple_rotate _ _ translated

structure Evidence (t : Template) (arity : Nat) : Prop where
  intervals : Cert t arity
  cycleOK : t.chart.cycle.ok=true
  indices : ∀ p∈t.chart.cycle.points,p.1<t.chart.x.length ∧ p.2<t.chart.y.length
  table : ∃ (cache : List Entry) (x y : List SignHint),
    let program := t.corridor.baseRows++t.corridor.rest
    let rows := program.reverse
    let bs := stack [] program
    cache.length=rows.length ∧ Verified rows bs cache 0 rows.length ∧
      RegisterOrder.check t rows bs cache false x=true ∧ RegisterOrder.check t rows bs cache true y=true

theorem realized {t : Template} {rs : List Nat} (ev : Evidence t rs.length) (n j : Nat)
    (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n) :
    let s := (1:ℚ)/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    let g := ShapeRefs.join (t.corridor.coords args) (t.room.coords s)
    (actual t.chart g).Simple := by
  let s := (1:ℚ)/n
  let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
  let p := t.corridor.baseRows++t.corridor.rest
  let xs := execRat args [] p
  obtain ⟨cache,xh,yh,size,valid,xc,yc⟩ := ev.table
  have big : (65:ℚ)≤n := by exact_mod_cast hn
  have pos : 0<getRat args 0 := by change 0<(1:ℚ)/n; positivity
  have small : getRat args 0≤cap := by
    change (1:ℚ)/n≤1/65
    exact one_div_le_one_div_of_le (by norm_num) big
  have run : Ledger args p.reverse xs := by simpa only [List.append_nil,xs] using exec_ledger (Ledger.nil (args:=args)) p
  have bounds := lookup_bound (xs:=[]) (parameters n j rs hn hj hr) (by exact empty_encloses) ev.intervals.arithmetic
  have m : Model args xs p.reverse (stack [] p) cache :=
    ⟨run,bounds,pos,small,RegisterTable.model run bounds pos small size valid⟩
  exact BoundaryChart.simple t.chart ev.cycleOK ev.indices _
    (RegisterOrder.axis m rfl false xh xc) (RegisterOrder.axis m rfl true yh yc)

theorem emitted {t : Template} {rs : List Nat} (ev : Evidence t rs.length) (n j : Nat)
    (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n) {e : Entrance} (hit : (drawOne t n j rs).1=some e) :
    (Polygon.mk (e.2.map ratPoint)).Simple := by
  change (atDoor (door j) (W n) _).map (fun v => (door j,v))=some e at hit
  obtain ⟨path,ok,rfl⟩ := Option.map_eq_some_iff.mp hit
  exact simple_at_door (realized ev n j hn hj hr) ok

end ArtGallery.Orthogonal.BoundaryPoint.WingOrderSound
end
