module

public import ArtGallery.Orthogonal.BoundaryPoint.ShapeRefs
public import ArtGallery.Orthogonal.BoundaryPoint.HighStep

/-! # Checking the high-step cut directly on every edge of a wing chart -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.DoorFenceCert
open ShapeRefs RoomCoordinates RoomPolynomials MarginCert LinearRegister ChartDrawing HighStep
open CorridorProgram BoundaryChart RectContour ContourJoin BankCoordinates

inductive Side where | east | north | channel

private theorem any_iff {α : Type} {o : Option α} {p : α → Bool} (h : o.any p=true) :
    ∃ a,o=some a ∧ p a=true := by cases o <;> simp_all

def above (rows : List Row) (bs : List Box) (a : Axis) (q : ℚ) : Ref → Bool
  | .origin => decide (q<0)
  | .register i => decide (q<(getBox bs i).lo) ||
      (read 8 rows i).any (fun f => decide (f.1=q ∧ 0<f.2))
  | .level i => ltP [q] ((axisPolys a).getD i [])

def atLeast (bs : List Box) (a : Axis) (q : ℚ) : Ref → Bool
  | .origin => decide (q≤0)
  | .register i => decide (q≤(getBox bs i).lo)
  | .level i => leP [q] ((axisPolys a).getD i [])

def rail (rows : List Row) : Ref → Bool
  | .origin => true
  | .level _ => false
  | .register i => (read 8 rows i).any fun f => decide (f.1=0 ∧ (f.2=0 ∨ f.2=1/320))

def accepts (rows : List Row) (bs : List Box) (x y : Axis) (a b : Ref × Ref) : Side → Bool
  | .east => above rows bs x (1101/10) a.1 && above rows bs x (1101/10) b.1
  | .north => above rows bs y 1 a.2 && above rows bs y 1 b.2
  | .channel => (rail rows a.1 && atLeast bs y 1 a.2) && (rail rows b.1 && atLeast bs y 1 b.2)

def check (t : Template) (hints : List Side) : Bool :=
  let v := axes t.chart (refs t)
  let rows := t.corridor.baseRows++t.corridor.rest
  (List.range v.length).all (fun i => accepts rows.reverse (stack [] rows) t.room.x t.room.y
    (v.getD i (0,0)) (v.getD ((i+1)%v.length) (0,0)) (hints.getD i .east))

private theorem poly_value (s : ℚ) (a : Axis) (i : Nat) :
    evalR s ((axisPolys a).getD i [])=(((a.coordsQ s).getD i 0 : ℚ):ℝ) := by
  rw [index_value,←cast_coords]
  simpa only [Rat.cast_zero] using List.getD_map (l:=a.coordsQ s) (d:=0) (n:=i) (fun q : ℚ => (q:ℝ))

structure Values (args xs : List ℚ) (p : List Row) (bs : List Box) : Prop where
  run : Ledger args p xs
  box : ∀ i,(getBox bs i).lo≤getRat xs i ∧ getRat xs i≤(getBox bs i).hi
  pos : 0<getRat args 0
  upper : (getRat args 0:ℝ)≤1/65

private theorem above_sound {v xs p bs} (data : Values v xs p bs) (a : Axis) (r : Ref) (q : ℚ)
    (pass : above p bs a q r=true) : q<readRef xs a (getRat v 0) r := by
  cases r with
  | origin => exact of_decide_eq_true pass
  | register i =>
    simp only [above,Bool.or_eq_true,decide_eq_true_eq] at pass
    rcases pass with gap|aff
    · exact gap.trans_le (data.box i).1
    · obtain ⟨f,ok,h⟩ := any_iff aff
      obtain ⟨h₁,h₂⟩ := of_decide_eq_true h
      change q<getRat xs i
      rw [read_value data.run 8 i ok,val,h₁]
      exact lt_add_of_pos_right _ (mul_pos h₂ data.pos)
  | level i =>
    have h := lt_sound (Rat.cast_pos.mpr data.pos) data.upper pass
    simp only [evalR,zero_mul,mul_zero,add_zero,poly_value] at h
    exact Rat.cast_lt.mp h

private theorem least_sound {v xs p bs} (data : Values v xs p bs) (a : Axis) (r : Ref) (q : ℚ)
    (pass : atLeast bs a q r=true) : q≤readRef xs a (getRat v 0) r := by
  cases r with
  | origin => exact of_decide_eq_true pass
  | register i => exact (of_decide_eq_true pass).trans (data.box i).1
  | level i =>
    have h := le_sound (Rat.cast_pos.mpr data.pos) data.upper pass
    simp only [evalR,mul_zero,add_zero,poly_value] at h
    exact Rat.cast_le.mp h

private theorem rail_sound {v xs p bs} (data : Values v xs p bs) (a : Axis) (r : Ref)
    (pass : rail p r=true) :
    0≤readRef xs a (getRat v 0) r ∧ readRef xs a (getRat v 0) r≤(1/320)*getRat v 0 := by
  cases r with
  | origin => exact ⟨le_refl _,mul_nonneg (by norm_num) data.pos.le⟩
  | level => contradiction
  | register i =>
    obtain ⟨f,ok,h⟩ := any_iff pass
    obtain ⟨base,cases⟩ := of_decide_eq_true h
    change 0≤getRat xs i ∧ getRat xs i≤_
    rw [read_value data.run 8 i ok,val,base,zero_add]
    rcases cases with zero|pos
    · rw [zero,zero_mul]; exact ⟨le_refl _,mul_nonneg (by norm_num) data.pos.le⟩
    · rw [pos]; exact ⟨mul_nonneg (by norm_num) data.pos.le,le_refl _⟩

theorem cyclic {args : List ℚ} {t : Template} (hints : List Side) {params : List Box}
    (encl : Encloses params (args.map ((↑) : ℚ → ℝ))) (arith : ok params [] (t.corridor.baseRows++t.corridor.rest)=true)
    (hs : 0<getRat args 0) (hu : (getRat args 0:ℝ)≤1/65) (pass : check t hints=true) :
    let s := getRat args 0
    let g := t.corridor.coords args
    let r := t.room.coords s
    Cyclic ((1/320)*s) (t.chart.draw (g.1++r.1,g.2++r.2)) := by
  let s := getRat args 0
  let p := t.corridor.baseRows++t.corridor.rest
  let xs := execRat args [] p
  let bs := stack [] p
  let V := axes t.chart (refs t)
  let coord (u : Ref × Ref) := (readRef xs t.room.x s u.1,readRef xs t.room.y s u.2)
  have data : Values args xs p.reverse bs :=
    ⟨by simpa [p,xs] using exec_ledger (Ledger.nil (args:=args)) p,
     lookup_bound (xs:=[]) encl (by exact empty_encloses) arith,hs,hu⟩
  change Cyclic ((1/320)*s) _ 
  rw [ShapeRefs.actual t args s]
  change Cyclic ((1/320)*s) (V.map coord)
  intro i hi
  simp only [List.length_map] at hi ⊢
  have get (j : Nat) : (V.map coord).getD j (0,0)=coord (V.getD j (0,0)) :=
    List.getD_map (l:=V) (d:=(0,0)) (n:=j) coord
  rw [get,get]
  let a := V.getD i (0,0)
  let b := V.getD ((i+1)%V.length) (0,0)
  have step : accepts p.reverse bs t.room.x t.room.y a b (hints.getD i .east)=true :=
    List.all_eq_true.mp pass i (List.mem_range.mpr hi)
  cases flag : hints.getD i .east with
  | east =>
    have h : above p.reverse bs t.room.x (1101/10) a.1=true ∧ above p.reverse bs t.room.x (1101/10) b.1=true := by
      simpa only [flag,accepts,Bool.and_eq_true] using step
    exact Or.inl ⟨above_sound data _ _ _ h.1,above_sound data _ _ _ h.2⟩
  | north =>
    have h : above p.reverse bs t.room.y 1 a.2=true ∧ above p.reverse bs t.room.y 1 b.2=true := by
      simpa only [flag,accepts,Bool.and_eq_true] using step
    exact Or.inr (Or.inl ⟨above_sound data _ _ _ h.1,above_sound data _ _ _ h.2⟩)
  | channel =>
    have h : (rail p.reverse a.1=true ∧ atLeast bs t.room.y 1 a.2=true) ∧
        (rail p.reverse b.1=true ∧ atLeast bs t.room.y 1 b.2=true) := by
      simpa only [flag,accepts,Bool.and_eq_true] using step
    have L := rail_sound data t.room.x _ h.1.1
    have R := rail_sound data t.room.x _ h.2.1
    exact Or.inr (Or.inr ⟨⟨L.1,L.2,least_sound data _ _ _ h.1.2⟩,⟨R.1,R.2,least_sound data _ _ _ h.2.2⟩⟩)

end ArtGallery.Orthogonal.BoundaryPoint.DoorFenceCert
end
