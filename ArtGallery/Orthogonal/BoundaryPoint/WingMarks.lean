module

public import ArtGallery.Orthogonal.BoundaryPoint.IndexedWing
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrderSound

/-! # Actual variable segments, stationary spots and pin witnesses on a wing
The data are read from the physical registers and arithmetic room. Each
request is either the complete allowed guard segment or a singleton. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingMarks
open Set MarginCert LinearRegister RegisterTable RegisterOrder ShapeRefs IndexedWing
open WingEnvelope BoundaryChart ChartDrawing CorridorProgram GridPins RoomGrid ArtGallery.Orthogonal.Hard

def perRole {α : Type} : List α → List (α × α)
  | [c,a,b,u,v,w] => [(c,c),(a,b),(u,u),(v,v),(w,w)]
  | _ => []
def requests {α : Type} (roles : List (List α)) := roles.flatMap perRole

private theorem per_map {α β : Type} (f : α → β) (l : List α) :
    perRole (l.map f)=(perRole l).map (Prod.map f f) := by
  rcases l with _|⟨a,l⟩; rfl
  rcases l with _|⟨b,l⟩; rfl
  rcases l with _|⟨c,l⟩; rfl
  rcases l with _|⟨d,l⟩; rfl
  rcases l with _|⟨e,l⟩; rfl
  rcases l with _|⟨g,l⟩; rfl
  cases l <;> rfl

theorem requests_map {α β : Type} (f : α → β) (ls : List (List α)) :
    requests (ls.map (List.map f))=(requests ls).map (Prod.map f f) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [requests,List.map_cons,List.flatMap_cons,List.map_append,per_map] at ih ⊢
    rw [ih]

private theorem cast_lookup (xs : List ℚ) (i : Nat) :
    ((xs.getD i 0:ℚ):ℝ)=(xs.map ((↑) : ℚ → ℝ)).getD i 0 := by
  simpa only [Rat.cast_zero] using (List.getD_map (l:=xs) (n:=i) (d:=0) (fun x : ℚ => (x:ℝ))).symm

def Holds (t : Template) (args : List ℚ) : Prop :=
  let g := ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))
  ∀ e∈requests g.2, ArtGallery.segment (ratPoint e.1) (ratPoint e.2)⊆(actual t.chart g).boundary

theorem certified {t : Template} {args xs rows bs cache} (m : Model args xs rows bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) {xh yh : List SignHint}
    (xc : RegisterOrder.check t rows bs cache false xh=true) (yc : RegisterOrder.check t rows bs cache true yh=true)
    (index : Data Nat) (rec : IndexedWing.check t rows cache index=true) (marks : List Mark)
    (listed : marks.map Prod.snd=requests index.2)
    (checked : marks.all (markOk t.chart.x.length t.chart.y.length t.chart.cycle.points)=true) : Holds t args := by
  let x := grid t args false
  let y := grid t args true
  let X := x.map ((↑) : ℚ → ℝ)
  let Y := y.map ((↑) : ℚ → ℝ)
  let pt (i : Index) := (x.getD i.1 0,y.getD i.2 0)
  let g := ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))
  have spec := IndexedWing.realized m run index rec
  have roles : g.2=index.2.map (List.map pt) := congrArg Prod.snd spec
  have lenx : X.length=t.chart.x.length := by simp [X,x,grid,selected,idsOf]
  have leny : Y.length=t.chart.y.length := by simp [Y,y,grid,selected,idsOf]
  have orderedX := RegisterOrder.axis m run false xh xc
  have orderedY := RegisterOrder.axis m run true yh yc
  have hits := GridPins.all_segments (xs:=X) (ys:=Y) orderedX orderedY (by rwa [lenx,leny])
  change ∀ e∈requests g.2,_ 
  intro e he
  rw [roles,requests_map] at he
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp he
  have point (i : Index) : ratPoint (pt i)=gridPt X Y i :=
    Prod.ext (cast_lookup x i.1) (cast_lookup y i.2)
  change ArtGallery.segment (ratPoint (pt u.1)) (ratPoint (pt u.2)) ⊆ (actual t.chart g).boundary
  rw [point,point,actual_grid]
  exact hits u (listed ▸ hu)

theorem at_size {t : Template} {rs : List Nat} (basic : WingEnvelopeCert.Cert t rs.length) (n j : Nat)
    (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n) {cache : List Entry} {xh yh : List SignHint}
    (index : Data Nat) (marks : List Mark)
    (tables : let p := t.corridor.baseRows++t.corridor.rest
      let rs := p.reverse
      let bs := stack [] p
      cache.length=rs.length ∧ Verified rs bs cache 0 rs.length ∧
      RegisterOrder.check t rs bs cache false xh=true ∧ RegisterOrder.check t rs bs cache true yh=true ∧
      IndexedWing.check t rs cache index=true)
    (listed : marks.map Prod.snd=requests index.2)
    (checked : marks.all (markOk t.chart.x.length t.chart.y.length t.chart.cycle.points)=true) :
    let s := (1:ℚ)/n
    Holds t (s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)) := by
  let s := (1:ℚ)/n
  let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
  let p := t.corridor.baseRows++t.corridor.rest
  let xs := execRat args [] p
  have pos : 0<getRat args 0 := by change 0<(1:ℚ)/n; positivity
  have small : getRat args 0≤RegisterForm.cap := by
    change (1:ℚ)/n≤1/65
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
  have run : Ledger args p.reverse xs := by simpa only [List.append_nil,xs] using exec_ledger (Ledger.nil (args:=args)) p
  have bounds := lookup_bound (xs:=[]) (WingEnvelopeCert.parameters n j rs hn hj hr) (by exact empty_encloses) basic.arithmetic
  obtain ⟨size,valid,xc,yc,rec⟩ := tables
  have m : Model args xs p.reverse (stack [] p) cache :=
    ⟨run,bounds,pos,small,RegisterTable.model run bounds pos small size valid⟩
  exact certified m rfl xc yc index rec marks listed checked

end ArtGallery.Orthogonal.BoundaryPoint.WingMarks
end
