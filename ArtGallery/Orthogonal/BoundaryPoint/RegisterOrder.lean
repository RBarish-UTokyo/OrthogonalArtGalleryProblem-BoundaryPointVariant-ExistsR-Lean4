module

public import ArtGallery.Orthogonal.BoundaryPoint.RegisterTable
public import ArtGallery.Orthogonal.BoundaryPoint.ShapeRefs

/-! # Strict coordinate order on the actual mixed staircase-room chart -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RegisterOrder
open MarginCert LinearRegister RegisterForm RegisterTable ShapeRefs ChartDrawing
open BoundaryChart RoomCoordinates RoomPolynomials

def polynomial : List ℚ → Form
  | [] => []
  | c::p => insert (0,0) c (scaled 1 1 (polynomial p))

theorem polynomial_value (s : ℚ) (A : Nat → ℚ) (one : A 0=1) (cs : List ℚ) :
    value s A (polynomial cs)=evalQ s cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [polynomial,insert_value,scaled_value,one,ih,evalQ,pow_zero,pow_one,one_mul,mul_one]

def expression (cache : List Entry) (a : Axis) : Ref → Form
  | .origin => []
  | .register i => form cache i
  | .level i => polynomial ((axisPolys a).getD i [])

private theorem poly_coord (a : Axis) (s : ℚ) (i : Nat) : evalQ s ((axisPolys a).getD i [])=(a.coordsQ s).getD i 0 := by
  apply (Rat.cast_inj (α:=ℝ)).mp
  rw [cast_eval,index_value,←cast_coords]
  simpa only [Rat.cast_zero] using List.getD_map (l:=a.coordsQ s) (d:=0) (n:=i) (fun q : ℚ => (q:ℝ))

structure Model (args xs : List ℚ) (rows : List Row) (bs : List Box) (cache : List Entry) : Prop where
  run : Ledger args rows xs
  bounds : ∀ i,(getBox bs i).lo≤getRat xs i ∧ getRat xs i≤(getBox bs i).hi
  pos : 0<getRat args 0
  upper : getRat args 0≤cap
  values : ∀ i,value (getRat args 0) (atomVal xs) (form cache i)=getRat xs i

theorem formula {args xs p bs cache} (m : Model args xs p bs cache) (a : Axis) (r : Ref) :
    value (getRat args 0) (atomVal xs) (expression cache a r)=readRef xs a (getRat args 0) r := by
  cases r with
  | origin => rfl
  | register i => exact m.values i
  | level i => exact (polynomial_value _ _ rfl _).trans (poly_coord ..)

def extent (bs : List Box) (cache : List Entry) (a : Axis) : Ref → Box
  | .register i => getBox bs i
  | r => boxForm (atomBox bs) (expression cache a r)

private theorem ext_bound {args xs p bs cache} (m : Model args xs p bs cache) (a : Axis) (r : Ref) :
    (extent bs cache a r).lo≤readRef xs a (getRat args 0) r ∧
      readRef xs a (getRat args 0) r≤(extent bs cache a r).hi := by
  cases r with
  | register i => exact m.bounds i
  | origin => exact ⟨le_refl _,le_refl _⟩
  | level i =>
    rw [←formula m]
    exact form_bound (atom_bound m.bounds) m.pos.le m.upper _

inductive SignHint where | boxes | power (k : Nat) | negativeAtom

def negToken (rows : List Row) (bs : List Box) : Form → Bool
  | [((_,i+1),c)] => decide (c<0) && negative rows bs i
  | _ => false

private theorem negToken_sound {args xs p bs cache} (m : Model args xs p bs cache) {f : Form}
    (h : negToken p bs f=true) : 0<value (getRat args 0) (atomVal xs) f := by
  unfold negToken at h; split at h
  next k i c =>
    have b : c<0 ∧ negative p bs i=true := by simpa only [Bool.and_eq_true,decide_eq_true_eq] using h
    have neg := negative_sound m.run m.pos (fun j => (m.bounds j).2) b.2
    simp only [value,valTerm,atomVal,add_zero]
    exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos b.1 (pow_pos m.pos k)) neg
  · contradiction

def ordered (rs : List Row) (bs : List Box) (cache : List Entry) (a : Axis) (l r : Ref) : SignHint → Bool
  | .boxes => decide ((extent bs cache a l).hi < (extent bs cache a r).lo)
  | .power k => positive (atomBox bs) (diff (expression cache a r) (expression cache a l)) k
  | .negativeAtom => negToken rs bs (diff (expression cache a r) (expression cache a l))

theorem ordered_sound {args xs p bs cache} (m : Model args xs p bs cache) (a : Axis) {l r : Ref}
    (hint : SignHint) (pass : ordered p bs cache a l r hint=true) :
    readRef xs a (getRat args 0) l<readRef xs a (getRat args 0) r := by
  cases hint with
  | boxes => exact ((ext_bound m a _).2.trans_lt (of_decide_eq_true pass)).trans_le (ext_bound m a _).1
  | power k =>
    have h := positive_value (atom_bound m.bounds) m.pos m.upper pass
    rwa [diff_value,formula m,formula m,sub_pos] at h
  | negativeAtom =>
    have h := negToken_sound m pass
    rwa [diff_value,formula m,formula m,sub_pos] at h

def axisOf (t : Template) (y : Bool) := if y then t.room.y else t.room.x
def idsOf (t : Template) (y : Bool) := if y then t.chart.y else t.chart.x

def check (t : Template) (rs : List Row) (bs : List Box) (cache : List Entry) (y : Bool) (hints : List SignHint) : Bool :=
  let v := selected (pool y (refs t)) (idsOf t y)
  (List.range (v.length-1)).all fun i => ordered rs bs cache (axisOf t y)
    (v.getD i 0) (v.getD (i+1) 0) (hints.getD i .boxes)

theorem axis {t : Template} {args xs p bs cache} (m : Model args xs p bs cache)
    (xs_eq : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) (y : Bool) (hints : List SignHint)
    (pass : check t p bs cache y hints=true) :
    let s := getRat args 0
    let g := ShapeRefs.join (t.corridor.coords args) (t.room.coords s)
    ((selected (pool y g) (idsOf t y)).map ((↑) : ℚ → ℝ)).IsChain (·<·) := by
  subst xs
  dsimp only
  rw [ShapeRefs.levels,List.map_map]
  let v := selected (pool y (refs t)) (idsOf t y)
  apply List.isChain_iff_getElem.mpr
  intro i h
  simp only [List.length_map] at h
  have bound : i+1<v.length := h
  have step := List.all_eq_true.mp pass i (List.mem_range.mpr (show i<v.length-1 by omega))
  have lt := ordered_sound m _ _ step
  simpa only [v,axisOf,List.getD_eq_getElem _ _ (by omega : i<v.length),
    List.getD_eq_getElem _ _ bound,List.getElem_map,Function.comp_apply,Rat.cast_lt] using lt

end ArtGallery.Orthogonal.BoundaryPoint.RegisterOrder
end
