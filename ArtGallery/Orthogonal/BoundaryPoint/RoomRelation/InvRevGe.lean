module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomFamily.InvRevGe
public import ArtGallery.Orthogonal.BoundaryPoint.SlotLines
public import Mathlib.Tactic.Ring

/-! Arithmetic on the actual hard-room slot records. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomRelation.InvRevGe
open RoomFamily.InvRevGe RoomGrid RoomCoordinates SlotLines ArtGallery.Orthogonal.Hard Geometry DerivedAlgebra
set_option maxRecDepth 14000

noncomputable def guard (s : ℝ) (i : Nat) (t : ℝ) : Point :=
  slot (gridPt (xAxis.coordsR s) (yAxis.coordsR s)) roles i t

private theorem x2 (s : ℝ) : (xAxis.coordsR s).getD 2 0=evalR s [(493/2), 0, (1/20020)] := by
  simp [xAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

private theorem x3 (s : ℝ) : (xAxis.coordsR s).getD 3 0=evalR s [(493/2), 0, (1/5005)] := by
  simp [xAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

private theorem x8 (s : ℝ) : (xAxis.coordsR s).getD 8 0=evalR s [(501/2), 0, (-1/5005), 0, (1/400800400)] := by
  simp [xAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

private theorem x9 (s : ℝ) : (xAxis.coordsR s).getD 9 0=evalR s [(501/2), 0, (-1/20020), 0, (1/400800400)] := by
  simp [xAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

private theorem y1 (s : ℝ) : (yAxis.coordsR s).getD 1 0=evalR s [(-4)] := by
  simp [yAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

theorem position_A (s t : ℝ) : guard s 0 t =
    (evalR s [(493/2), 0, (1/20020)]+t*(2/3)*(evalR s [(493/2), 0, (1/5005)]-evalR s [(493/2), 0, (1/20020)]),(-4)) := by
  unfold guard slot
  dsimp only
  change lerp ((xAxis.coordsR s).getD 2 0,(yAxis.coordsR s).getD 1 0)
    ((xAxis.coordsR s).getD 3 0,(yAxis.coordsR s).getD 1 0) (t*(2/3))=_
  rw [x2,x3,y1]
  ext <;> simp [lerp,evalR] <;> ring

theorem position_B (s t : ℝ) : guard s 1 t =
    (evalR s [(501/2), 0, (-1/5005), 0, (1/400800400)]+t*(2/3)*(evalR s [(501/2), 0, (-1/20020), 0, (1/400800400)]-evalR s [(501/2), 0, (-1/5005), 0, (1/400800400)]),(-4)) := by
  unfold guard slot
  dsimp only
  change lerp ((xAxis.coordsR s).getD 8 0,(yAxis.coordsR s).getD 1 0)
    ((xAxis.coordsR s).getD 9 0,(yAxis.coordsR s).getD 1 0) (t*(2/3))=_
  rw [x8,x9,y1]
  ext <;> simp [lerp,evalR] <;> ring

theorem physical_axis (s x y : ℝ) (hs : 0<s) (hu : s≤1/65)
    (hx : InRange x) (hy : InRange y) :
    let v := s^2/50050
    let E := 2/(5*v)
    let A : Point := (-E,2)
    let B : Point := (-1/(2*E),4)
    (rayY (guard s 0 (x-1/2)) (world v A) (501/2) -
      rayY (guard s 1 (y-1/2)) (world v B) (501/2))*12 =
      2*(x*(5/2-y)-1)/((E-x)*((5/2-y)-1/E)) := by
  let v := s^2/50050
  let E := 2/(5*v)
  have hv : 0<v := by dsimp [v]; positivity
  have hE : 100≤E := by
    apply (le_div_iff₀ (show 0<5*v by positivity)).mpr
    dsimp [v]; nlinarith [mul_le_mul hu hu hs.le (by norm_num : (0:ℝ)≤1/65)]
  have hn : E≠0 := by linarith
  let ga : Point := (x-2*E,0)
  let gb : Point := (y-(5/2-1/(2*E)),0)
  let ca : Point := (-E,2)
  let cb : Point := (-1/(2*E),4)
  change (rayY (guard s 0 _) (world v ca) _ - rayY (guard s 1 _) (world v cb) _)*12=_
  have pa : guard s 0 (x-1/2)=world v ga := by
    rw [position_A]; ext <;> dsimp [ga,world,E,v,evalR] <;> field_simp [hs.ne'] <;> ring
  have pb : guard s 1 (y-1/2)=world v gb := by
    rw [position_B]; ext <;> dsimp [gb,world,E,v,evalR] <;> field_simp [hs.ne'] <;> ring
  rw [pa,pb]
  have wa := ray_world hv ga ca 0
  have wb := ray_world hv gb cb 0
  simp only [mul_zero,add_zero] at wa wb
  rw [wa,wb]
  have huA := (InversionCriticalAlgebra.denominators_pos hE hx (show InRange (5/2-y) by rcases hy with ⟨l,r⟩; constructor <;> linarith))
  have aa : rayY ga ca 0=InversionCriticalAlgebra.revA E x 0 := by
    dsimp [rayY,ga,ca,InversionCriticalAlgebra.revA]
    field_simp [hn,sub_ne_zero.mpr huA.1.ne'] <;> ring
  have bb : rayY gb cb 0=InversionCriticalAlgebra.revB E (5/2-y) 0 := by
    dsimp [rayY,gb,cb,InversionCriticalAlgebra.revB]
    field_simp [hn,sub_ne_zero.mpr huA.2.ne'] <;> ring
  rw [aa,bb]
  have e := InversionCriticalAlgebra.rev_axis_difference hE hx (show InRange (5/2-y) by rcases hy with ⟨l,r⟩; constructor <;> linarith)
  calc
    _ = InversionCriticalAlgebra.revA E x 0 - InversionCriticalAlgebra.revB E (5/2-y) 0 := by ring
    _ = _ := e

end ArtGallery.Orthogonal.BoundaryPoint.RoomRelation.InvRevGe
end
