module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomCoordinates
public import ArtGallery.Geometry.Det
public import Mathlib.Data.List.GetD
public import ArtGallery.Orthogonal.Hard.RatEq

/-! # Checked signs of univariate room projection determinants

Lists encode Horner polynomials in the reciprocal gallery size. A hint
supplies the number of leading vanishing coefficients. A rational bound on
the remaining Horner polynomial then proves a weak or strict sign for every
positive scale up to 1/65. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomPolynomials
open RoomCoordinates Geometry

abbrev P := List ℚ
abbrev Pt := P × P

def plus : P → P → P
  | [],q => q
  | p,[] => p
  | a::p,b::q => (a+b)::plus p q

def minus (p : P) : P := p.map Neg.neg
def subP (p q : P) := plus p (minus q)
def scale (a : ℚ) (p : P) : P := p.map (a*·)
def times : P → P → P
  | [],_ => []
  | a::p,q => plus (scale a q) (0::times p q)

theorem eval_plus (s : ℝ) (p q : P) : evalR s (plus p q)=evalR s p+evalR s q := by
  induction p generalizing q with
  | nil => simp [plus,evalR]
  | cons a p ih =>
    cases q with
    | nil => simp [plus,evalR]
    | cons b q => simp only [plus,evalR,ih,Rat.cast_add]; ring

theorem eval_minus (s : ℝ) (p : P) : evalR s (minus p)= -evalR s p := by
  induction p with
  | nil => simp [minus,evalR]
  | cons a p ih =>
    simp only [minus,List.map_cons,evalR,Rat.cast_neg]
    change -(a:ℝ)+s*evalR s (minus p)=_
    rw [ih]; ring

theorem eval_sub (s : ℝ) (p q : P) : evalR s (subP p q)=evalR s p-evalR s q := by
  rw [subP,eval_plus,eval_minus,sub_eq_add_neg]

theorem eval_scale (s : ℝ) (a : ℚ) (p : P) : evalR s (scale a p)=(a:ℝ)*evalR s p := by
  induction p with
  | nil => simp [scale,evalR]
  | cons b p ih =>
    change ((a*b:ℚ):ℝ)+s*evalR s (scale a p)=_
    rw [ih,Rat.cast_mul]; simp only [evalR]; ring

theorem eval_times (s : ℝ) (p q : P) : evalR s (times p q)=evalR s p*evalR s q := by
  induction p with
  | nil => simp [times,evalR]
  | cons a p ih =>
    rw [times,eval_plus,eval_scale]
    simp only [evalR,Rat.cast_zero,zero_add,ih]; ring

def oriented (a b c : Pt) : P :=
  subP (times (subP b.1 a.1) (subP c.2 a.2)) (times (subP b.2 a.2) (subP c.1 a.1))
noncomputable def pt (s : ℝ) (a : Pt) : Point := (evalR s a.1,evalR s a.2)

theorem eval_oriented (s : ℝ) (a b c : Pt) :
    evalR s (oriented a b c)=det (pt s a) (pt s b) (pt s c) := by
  simp only [oriented,eval_sub,eval_times,pt,det]; ring

private theorem andParts {a b : Bool} (h : (a && b)=true) : a=true ∧ b=true := by
  simpa only [Bool.and_eq_true] using h

def startsZero : Nat → P → Bool
  | 0,_ => true
  | _+1,[] => true
  | k+1,c::p => decide (c=0) && startsZero k p

def positive (p : P) (k : Nat) : Bool := startsZero k p && decide (0<lower (p.drop k))

theorem remove_power {p : P} {k : Nat} (ok : startsZero k p=true) (s : ℝ) :
    evalR s p = s^k*evalR s (p.drop k) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    cases p with
    | nil => simp [evalR]
    | cons a p =>
      obtain ⟨h,hp⟩ := andParts ok
      obtain rfl := of_decide_eq_true h
      simp only [evalR,Rat.cast_zero,zero_add,List.drop_succ_cons,pow_succ]
      rw [ih hp]; ring

theorem positive_sound {p : P} {k : Nat} (ok : positive p k=true)
    {s : ℝ} (hs : 0<s) (hu : s≤1/65) : 0<evalR s p := by
  obtain ⟨zeros,h⟩ := andParts ok
  have pos := Rat.cast_pos (K:=ℝ) |>.mpr (of_decide_eq_true h)
  rw [remove_power zeros]
  exact mul_pos (pow_pos hs _) (pos.trans_le (lower_le _ hs.le hu))

theorem zero_sound {p : P} (ok : p.all (fun a => decide (a=0))=true) (s : ℝ) : evalR s p=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    obtain ⟨zero,rest⟩ := andParts ok
    obtain rfl := of_decide_eq_true zero
    simp [evalR,ih rest]

def strict (p : P) := positive p (p.takeWhile (fun q => decide (q=0))).length
def weak (p : P) := (p.all fun q => decide (q=0)) || strict p
def ltP (p q : P) := strict (subP q p)
def leP (p q : P) := weak (subP q p)

theorem strict_sound {p : P} {s : ℝ} (hs : 0<s) (hu : s≤1/65) (h : strict p=true) :
    0<evalR s p := positive_sound h hs hu

theorem weak_sound {p : P} {s : ℝ} (hs : 0<s) (hu : s≤1/65) (h : weak p=true) :
    0≤evalR s p := by
  have hh : (p.all fun q => decide (q=0))=true ∨ strict p=true := by simpa only [weak,Bool.or_eq_true] using h
  rcases hh with z|sg
  · exact (zero_sound z s).ge
  · exact (strict_sound hs hu sg).le

theorem lt_sound {p q : P} {s : ℝ} (hs : 0<s) (hu : s≤1/65) (h : ltP p q=true) :
    evalR s p<evalR s q := by simpa only [eval_sub,sub_pos] using strict_sound hs hu h

theorem le_sound {p q : P} {s : ℝ} (hs : 0<s) (hu : s≤1/65) (h : leP p q=true) :
    evalR s p≤evalR s q := by simpa only [eval_sub,sub_nonneg] using weak_sound hs hu h

def coeffLevels (p : P) : List Gap → List P
  | [] => [p]
  | g::gs => p::coeffLevels (plus p (List.replicate g.order 0++g.coefficients)) gs

def axisPolys (a : Axis) := coeffLevels a.initial a.gaps

theorem eval_pad (s : ℝ) (k : Nat) (p : P) : evalR s (List.replicate k 0++p)=s^k*evalR s p := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ,List.cons_append,evalR,Rat.cast_zero,zero_add,ih,pow_succ]; ring

theorem coeff_levels (s : ℝ) (p : P) (gs : List Gap) :
    (coeffLevels p gs).map (evalR s) = positions (fun g => g.valR s) (evalR s p) gs := by
  induction gs generalizing p with
  | nil => rfl
  | cons g gs ih => simp only [coeffLevels,List.map_cons,ih,eval_plus,eval_pad,positions,Gap.valR]

theorem index_value (s : ℝ) (a : Axis) (i : Nat) :
    evalR s ((axisPolys a).getD i []) = (a.coordsR s).getD i 0 := by
  have h := List.getD_map (l:=axisPolys a) (d:=[]) (n:=i) (evalR s)
  rw [← h]; exact congrArg (fun (l : List ℝ) => l.getD i 0) (coeff_levels s a.initial a.gaps)

def polyNode (a b : Axis) (i : RoomGrid.Index) : Pt := ((axisPolys a).getD i.1 [],(axisPolys b).getD i.2 [])

theorem node_value (s : ℝ) (a b : Axis) (i : RoomGrid.Index) :
    pt s (polyNode a b i)=ArtGallery.Orthogonal.Hard.gridPt (a.coordsR s) (b.coordsR s) i := by
  simp only [pt,polyNode,ArtGallery.Orthogonal.Hard.gridPt,index_value]

end ArtGallery.Orthogonal.BoundaryPoint.RoomPolynomials
end
