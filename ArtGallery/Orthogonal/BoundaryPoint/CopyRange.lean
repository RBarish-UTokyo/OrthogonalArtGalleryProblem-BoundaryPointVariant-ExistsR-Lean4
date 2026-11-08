module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyMatch
public import ArtGallery.Orthogonal.BoundaryPoint.RegBranch

/-! # Signs of determinants and linear forms from lifted closed forms

Every quantity `v` of a range condition is lifted to `V=v*L` over a common
denominator `L≠0`. A determinant of three lifted points and a linear form
multiplied by the lifted unit are homogeneous of degree two, so they equal
`L^2` times the real expression, and the sign of an explicit polynomial
(certified by `PolyBox` on the parameter box, identity by `KronCert`) is the
sign of the real expression. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange
open KronCert PolyBox CopyMatch RegBranch

/-- The determinant tree of three lifted points. -/
def detX (wx wy gx gy cx cy : Ex) : Ex :=
  .sub (.mul (.sub gx wx) (.sub cy wy)) (.mul (.sub gy wy) (.sub cx wx))

/-- An integer linear combination of lifted quantities, times the lifted unit. -/
def linX (one : Ex) : List (Int × Ex) → Ex
  | [] => .lit []
  | (c,e)::t => .add (.mul (.mul (.lit [[[c]]]) e) one) (linX one t)

noncomputable def linR : List (Int × ℝ) → ℝ
  | [] => 0
  | (c,v)::t => c*v+linR t

theorem detX_ev {x y z L : ℝ} {wx wy gx gy cx cy : Ex} {a b c d e f : ℝ}
    (h1 : wx.ev x y z=a*L) (h2 : wy.ev x y z=b*L) (h3 : gx.ev x y z=c*L) (h4 : gy.ev x y z=d*L)
    (h5 : cx.ev x y z=e*L) (h6 : cy.ev x y z=f*L) :
    (detX wx wy gx gy cx cy).ev x y z=L^2*ArtGallery.det (a,b) (c,d) (e,f) := by
  simp only [detX,Ex.ev,h1,h2,h3,h4,h5,h6,ArtGallery.det]; ring

theorem linX_ev {x y z L : ℝ} {one : Ex} (hone : one.ev x y z=L) :
    ∀ (ts : List (Int × Ex)) (vs : List (Int × ℝ)), List.Forall₂ (fun t v => t.1=v.1 ∧ t.2.ev x y z=v.2*L) ts vs →
      (linX one ts).ev x y z=L^2*linR vs
  | [],[],_ => by simp [linX,linR,Ex.ev,ev3]
  | (c,e)::ts,(c',v)::vs,h => by
    obtain ⟨⟨hc,he⟩,ht⟩ := List.forall₂_cons.mp h
    simp only at hc he
    simp only [linX,linR,Ex.ev,he,hone,linX_ev hone ts vs ht,hc,ev3,ev2,ev1]; push_cast; ring

/-- A sign certificate: the literal `P` equals the tree, and `σ*P>0` on the box. -/
def signed (c bl bh : ℚ) (e P : Ex) (σ : Int) : Bool :=
  RegCert.auto (.sub e P) && signPos c bl bh σ P

theorem signed_sound {c bl bh : ℚ} {x y z : ℝ} (B : Box c bl bh x y z) {e P : Ex} {σ : Int}
    (h : signed c bl bh e P σ=true) {L r : ℝ} (hL : L≠0) (he : e.ev x y z=L^2*r) : 0<σ*r := by
  simp only [signed,Bool.and_eq_true] at h
  obtain ⟨hid,hp⟩ := h
  have i := Ex.sound hid x y z
  simp only [Ex.ev] at i
  have p := signPos_sound B hp
  rw [←sub_eq_zero.mp i,he] at p
  have hL2 : 0<L^2 := by positivity
  have : (σ:ℝ)*(L^2*r)=L^2*(σ*r) := by ring
  rw [this] at p
  exact pos_of_mul_pos_right p hL2.le

theorem lift_ev {x y z v : ℝ} {L N D C : Ex} (h : Lift x y z v L N D C) :
    (Ex.mul N C).ev x y z=v*L.ev x y z := h.eq

/-- An identity certificate: the tree vanishes identically. -/
theorem zero_of_check {x y z : ℝ} {e : Ex} (h : RegCert.auto e=true) {L r : ℝ} (hL : L≠0)
    (he : e.ev x y z=L^2*r) : r=0 := by
  have := Ex.sound h x y z
  rw [he] at this
  rcases mul_eq_zero.mp this with h|h
  · exact absurd (pow_eq_zero_iff (n:=2) (by norm_num) |>.mp h) hL
  · exact h

/-- The spot-length tree: `2*(u-v)*w-3*(1-q)` homogenised. -/
def spotX (u v w q one : Ex) : Ex :=
  .sub (.mul (.mul (.lit [[[2]]]) (.sub u v)) w) (.mul (.mul (.lit [[[3]]]) (.sub one q)) one)

theorem spotX_ev {x y z L : ℝ} {u v w q one : Ex} {a b c d : ℝ}
    (h1 : u.ev x y z=a*L) (h2 : v.ev x y z=b*L) (h3 : w.ev x y z=c*L) (h4 : q.ev x y z=d*L) (h5 : one.ev x y z=L) :
    (spotX u v w q one).ev x y z=L^2*(2*(a-b)*c-3*(1-d)) := by
  simp only [spotX,Ex.ev,h1,h2,h3,h4,h5,ev3,ev2,ev1]; push_cast; ring

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange
end
