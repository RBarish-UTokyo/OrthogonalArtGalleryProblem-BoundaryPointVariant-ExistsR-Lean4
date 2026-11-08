module

public import ArtGallery.Orthogonal.BoundaryPoint.RegisterOrder

/-! # Comparing the two products of coordinate gaps of a physical aperture -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RegisterProduct
open RegisterForm MarginCert

def productBox (a b : Box) : Box :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩

private theorem middle {l h a b x y : ℚ} (lo : a≤x) (hi : x≤b)
    (A : l≤a*y ∧ a*y≤h) (B : l≤b*y ∧ b*y≤h) : l≤x*y ∧ x*y≤h := by
  rcases le_total 0 y with pos|neg
  · exact ⟨A.1.trans (mul_le_mul_of_nonneg_right lo pos),(mul_le_mul_of_nonneg_right hi pos).trans B.2⟩
  · exact ⟨B.1.trans (mul_le_mul_of_nonpos_right hi neg),(mul_le_mul_of_nonpos_right lo neg).trans A.2⟩

theorem product_bound {u v : ℚ} {a b : Box} (A : a.lo≤u ∧ u≤a.hi) (B : b.lo≤v ∧ v≤b.hi) :
    (productBox a b).lo≤u*v ∧ u*v≤(productBox a b).hi := by
  apply middle A.1 A.2
  · rw [mul_comm]; apply middle B.1 B.2
    · rw [mul_comm]; exact ⟨(min_le_left ..).trans (min_le_left ..),(le_max_left ..).trans (le_max_left ..)⟩
    · rw [mul_comm]; exact ⟨(min_le_left ..).trans (min_le_right ..),(le_max_right ..).trans (le_max_left ..)⟩
  · rw [mul_comm]; apply middle B.1 B.2
    · rw [mul_comm]; exact ⟨(min_le_right ..).trans (min_le_left ..),(le_max_left ..).trans (le_max_right ..)⟩
    · rw [mul_comm]; exact ⟨(min_le_right ..).trans (min_le_right ..),(le_max_right ..).trans (le_max_right ..)⟩

abbrev Hint := Nat × Nat × Nat × Nat
def subform (k l : Nat) : Form := [((k,1),1),((l,2),-1)]
def twoBoxes (x y : Box) : Nat → Box
  | 1 => x | 2 => y | _ => ⟨0,0⟩
def twoVals (x y : ℚ) : Nat → ℚ
  | 1 => x | 2 => y | _ => 0

def check (B : Nat → Box) (a b c d : Form) (h : Hint) :=
  let (i,j,k,l) := h
  let reduced (z : Form) (n : Nat) := boxForm B (dropPower n z)
  (divides i a && divides j b) && ((divides k c && divides l d) &&
    positive (twoBoxes (productBox (reduced a i) (reduced b j)) (productBox (reduced c k) (reduced d l)))
      (subform (i+j) (k+l)) (min (i+j) (k+l)))

theorem compare {B A} (bounds : Bounds B A) {s : ℚ} (hs : 0<s) (hu : s≤cap)
    {a b c d : Form} (h : Hint) (pass : check B a b c d h=true) :
    value s A c*value s A d<value s A a*value s A b := by
  obtain ⟨i,j,k,l⟩ := h
  simp only [check,Bool.and_eq_true] at pass
  obtain ⟨⟨ha,hb⟩,⟨hc,hd⟩,good⟩ := pass
  let R (f : Form) (t : Nat) := value s A (dropPower t f)
  let Q (f : Form) (t : Nat) := boxForm B (dropPower t f)
  let U := R a i * R b j
  let V := R c k * R d l
  let Ubox := productBox (Q a i) (Q b j)
  let Vbox := productBox (Q c k) (Q d l)
  have envelop : Bounds (twoBoxes Ubox Vbox) (twoVals U V) := by
    intro idx; rcases idx with _|⟨_|⟨_|idx⟩⟩
    · exact ⟨le_refl _,le_refl _⟩
    · exact product_bound (form_bound bounds hs.le hu _) (form_bound bounds hs.le hu _)
    · exact product_bound (form_bound bounds hs.le hu _) (form_bound bounds hs.le hu _)
    · exact ⟨le_refl _,le_refl _⟩
  have sign := positive_value envelop hs hu good
  change 0<value s (twoVals U V) (subform (i+j) (k+l)) at sign
  simp only [subform,value,valTerm,twoVals,one_mul,add_zero,neg_one_mul,pow_add] at sign
  rw [factored hc,factored hd,factored ha,factored hb]
  dsimp only [U,V,R] at sign
  linarith only [sign]

end ArtGallery.Orthogonal.BoundaryPoint.RegisterProduct
end
