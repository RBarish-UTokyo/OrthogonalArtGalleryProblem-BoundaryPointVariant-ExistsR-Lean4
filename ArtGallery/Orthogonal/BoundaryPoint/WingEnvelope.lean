module

public import ArtGallery.Orthogonal.BoundaryPoint.DoorRead
public import ArtGallery.Orthogonal.BoundaryPoint.RoomPolynomials
public import ArtGallery.Existence.Base

/-! # Enclosures of the executed wing, including its Jordan-filled set
The coordinate pool contains the corners of every rectangle and the marked
points of every role. The default coordinate is inside both intervals. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingEnvelope
open BoundaryChart CorridorProgram PlanGeometry MarginCert LinearRegister RoomPolynomials RoomCoordinates
open RectContour ContourJoin BankCoordinates

def lo (y : Bool) : ℚ := if y then -5 else -20
def hi (y : Bool) : ℚ := if y then 10 else 1500
def Within (y : Bool) (q : ℚ) := lo y ≤ q ∧ q ≤ hi y
def Enclosed (g : Data ℚ) := ∀ y q, q∈pool y g → Within y q

private theorem zero (y : Bool) : Within y 0 := by cases y <;> norm_num [Within,lo,hi]

def mapData {α β : Type} (x y : α → β) (g : Data α) : Data β :=
  (g.1.map (fun r => (x r.1,x r.2.1,y r.2.2.1,y r.2.2.2)),
   g.2.map (fun v => v.map fun p => (x p.1,y p.2)))

theorem map_pool {α β : Type} (x y : α → β) (g : Data α) (v : Bool) :
    pool v (mapData x y g)=(pool v g).map (if v then y else x) := by
  cases v <;> simp [pool,mapData,List.flatMap_map,List.map_flatMap,Function.comp_def]

theorem merge {a b : Data ℚ} (ha : Enclosed a) (hb : Enclosed b) :
    Enclosed (a.1++b.1,a.2++b.2) := by
  intro ax q hq
  simp only [pool,List.flatMap_append,List.flatten_append,List.map_append,List.mem_append] at hq
  rcases hq with (h|h)|(h|h)
  · exact ha ax q (List.mem_append_left _ h)
  · exact hb ax q (List.mem_append_left _ h)
  · exact ha ax q (List.mem_append_right _ h)
  · exact hb ax q (List.mem_append_right _ h)

def stairOK (t : Layout) (bs : List Box) (ax : Bool) : Bool :=
  (pool ax (t.cells,t.roles)).all fun i => decide (lo ax ≤ (getBox bs i).lo ∧ (getBox bs i).hi ≤ hi ax)

theorem staircase {t : Layout} {params : List Box} {args : List ℚ}
    (encl : Encloses params (args.map ((↑) : ℚ → ℝ))) (checks : ok params [] (t.baseRows++t.rest)=true)
    (pass : ∀ ax, stairOK t (stack [] (t.baseRows++t.rest)) ax=true) : Enclosed (t.coords args) := by
  let xs := execRat args [] (t.baseRows++t.rest)
  have read : t.coords args=mapData (getRat xs) (getRat xs) (t.cells,t.roles) := by
    simp [Layout.coords,mapData,xs,exec_append,readRect,readRole]
  intro ax q hq
  rw [read,map_pool,ite_self] at hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  have b := of_decide_eq_true (List.all_eq_true.mp (pass ax) i hi)
  have h := lookup_bound (xs:=[]) encl (by exact empty_encloses) checks i
  exact ⟨b.1.trans h.1,h.2.trans b.2⟩

def roomOK (k : Bool) (a : Axis) : Bool :=
  (axisPolys a).all fun p => leP [lo k] p && leP p [hi k]

private theorem get_ok {α : Type} {P : α → Prop} {l : List α} {d : α}
    (base : P d) (all : ∀ x∈l,P x) (j : Nat) : P (l.getD j d) := by
  by_cases h : j<l.length
  · rw [List.getD_eq_getElem l d h]; exact all _ (List.getElem_mem h)
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt h)] using base

theorem room_axis {ax : Bool} {a : Axis} (pass : roomOK ax a=true)
    {s : ℚ} (hs : 0<s) (hu : s≤1/65) (i : Nat) : Within ax ((a.coordsQ s).getD i 0) := by
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  have hu' : (s:ℝ)≤1/65 := by simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr hu
  have all (p) (hp : p∈axisPolys a) : (lo ax:ℝ)≤evalR s p ∧ evalR s p≤(hi ax:ℝ) := by
    have pair : leP [lo ax] p=true ∧ leP p [hi ax]=true := by simpa only [Bool.and_eq_true] using List.all_eq_true.mp pass p hp
    obtain ⟨L,H⟩ := pair
    exact ⟨by simpa [evalR] using le_sound hs' hu' L,by simpa [evalR] using le_sound hs' hu' H⟩
  have base : (lo ax:ℝ)≤evalR s [] ∧ evalR s []≤(hi ax:ℝ) := by
    cases ax <;> norm_num [lo,hi,evalR]
  have b := get_ok (P:=fun p => (lo ax:ℝ)≤evalR s p ∧ evalR s p≤(hi ax:ℝ)) base all i
  have cv : ((a.coordsQ s).map (fun q : ℚ => (q:ℝ))).getD i 0=(((a.coordsQ s).getD i 0:ℚ):ℝ) := by
    simpa only [Rat.cast_zero] using (List.getD_map (l:=a.coordsQ s) (d:=0) (n:=i) (fun q : ℚ => (q:ℝ)))
  rw [index_value,← cast_coords,cv] at b
  exact ⟨Rat.cast_le.mp b.1,Rat.cast_le.mp b.2⟩

theorem room (r : ArithmeticRoom) {s : ℚ} (hs : 0<s) (hu : s≤1/65)
    (hx : roomOK false r.x=true) (hy : roomOK true r.y=true) : Enclosed (r.coords s) := by
  intro b q h
  change q∈pool b (mapData (fun i => (r.x.coordsQ s).getD i 0) (fun i => (r.y.coordsQ s).getD i 0)
    (r.cells,r.roles)) at h
  rw [map_pool] at h
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
  cases b
  · exact room_axis hx hs hu _
  · exact room_axis hy hs hu _

private theorem picked {g : Data ℚ} (encl : Enclosed g) (b : Bool) (ids : List Nat) (i : Nat) :
    Within b ((selected (pool b g) ids).getD i 0) := by
  apply get_ok (zero b)
  intro q h
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
  exact get_ok (zero b) (encl b) j

theorem drawn (c : Chart) {g : Data ℚ} (h : Enclosed g) {p : Vertex} (hp : p∈c.draw g) :
    Within false p.1 ∧ Within true p.2 := by
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
  exact ⟨picked h false c.x j.1,picked h true c.y j.2⟩

theorem at_door {d w : ℚ} {cycle path : List Vertex} (out : atDoor d w cycle=some path)
    (bounds : ∀ q∈cycle, Within false q.1 ∧ Within true q.2) {p : Vertex} (hp : p∈path) :
    d-20≤p.1 ∧ p.1≤d+1500 ∧ -5≤p.2 ∧ p.2≤10 := by
  unfold atDoor at out
  dsimp only at out
  split at out
  · contradiction
  · obtain rfl := Option.some.inj out
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    have hit : q∈cycle := by
      rcases List.mem_append.mp hq with h|h
      · exact List.mem_of_mem_drop h
      · exact List.mem_of_mem_take h
    obtain ⟨⟨L,R⟩,B,T⟩ := bounds q hit
    change -20≤q.1 at L
    change q.1≤1500 at R
    exact ⟨by dsimp; linarith, by dsimp; linarith,B,T⟩

private theorem filled_interval {P : Polygon} {f : Point → ℝ}
    (aff : ∀ a b t, f (Geometry.lerp a b t)=(1-t)*f a+t*f b)
    (onto : Function.Surjective f) {l u : ℝ}
    (h : ∀ v∈P.vertices, l≤f v ∧ f v≤u) {q : Point} (hq : q∈P.filled) : l≤f q ∧ f q≤u := by
  have vertex (i : Nat) (hi : i<P.n) : l≤f (P.vtx i) ∧ f (P.vtx i)≤u := by
    unfold Polygon.vtx
    rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  have wall (p : Point) (hp : p∈P.boundary) : l≤f p ∧ f p≤u := by
    obtain ⟨i,hi,hp⟩ := hp
    obtain ⟨t,ht,h1,rfl⟩ := Geometry.mem_segment_iff_lerp.mp hp
    have a := vertex i hi
    have b := vertex ((i+1)%P.n) (Nat.mod_lt _ (by omega : 0<P.n))
    rw [aff]
    constructor
    · nlinarith only [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr a.1),mul_nonneg ht (sub_nonneg.mpr b.1)]
    · nlinarith only [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr a.2),mul_nonneg ht (sub_nonneg.mpr b.2)]
  constructor
  · by_contra! bad
    obtain ⟨v,hv⟩ := onto (l+1)
    exact Existence.not_mem_filled_of_neg_affine (T:=P.boundary) (Set.Subset.rfl)
      (f:=fun p => f p-l) (fun p hp => sub_nonneg.mpr (wall p hp).1)
      (v:=v) (fun t => by rw [aff]; ring) (by linarith) (sub_neg.mpr bad) hq
  · by_contra! bad
    obtain ⟨v,hv⟩ := onto (u-1)
    exact Existence.not_mem_filled_of_neg_affine (T:=P.boundary) (Set.Subset.rfl)
      (f:=fun p => u-f p) (fun p hp => sub_nonneg.mpr (wall p hp).2)
      (v:=v) (fun t => by rw [aff]; ring) (by linarith) (sub_neg.mpr bad) hq

def InStrip (j : Nat) (q : Point) : Prop :=
  (door j:ℝ)-20≤q.1 ∧ q.1≤(door j:ℝ)+1500 ∧ -5≤q.2 ∧ q.2≤10

theorem enclosure {j : Nat} {vs : List Vertex}
    (h : ∀ p∈vs, door j-20≤p.1 ∧ p.1≤door j+1500 ∧ -5≤p.2 ∧ p.2≤10)
    {q : Point} (hq : q∈(Polygon.mk (vs.map ratPoint)).filled) : InStrip j q := by
  have rect : ∀ p∈vs.map ratPoint, InStrip j p := by
    intro p hp
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hp
    have b := h u hu
    simp only [InStrip,ratPoint]
    exact_mod_cast b
  have x := filled_interval (f:=Prod.fst) (fun a b t => by simp; ring)
    (fun x => ⟨(x,0),rfl⟩) (fun p hp => ⟨(rect p hp).1,(rect p hp).2.1⟩) hq
  have y := filled_interval (f:=Prod.snd) (fun a b t => by simp; ring)
    (fun y => ⟨(0,y),rfl⟩) (fun p hp => (rect p hp).2.2) hq
  exact ⟨x.1,x.2,y⟩

theorem separate {j k : Nat} (ne : j≠k) {q : Point} (a : InStrip j q) (b : InStrip k q) : False := by
  unfold InStrip door at a b
  push_cast at a b
  rcases lt_or_gt_of_ne ne with t|t
  · have s : (j:ℝ)+1≤k := by exact_mod_cast t
    linarith [a.1,b.2.1]
  · have s : (k:ℝ)+1≤j := by exact_mod_cast t
    linarith [b.1,a.2.1]

end ArtGallery.Orthogonal.BoundaryPoint.WingEnvelope
end
