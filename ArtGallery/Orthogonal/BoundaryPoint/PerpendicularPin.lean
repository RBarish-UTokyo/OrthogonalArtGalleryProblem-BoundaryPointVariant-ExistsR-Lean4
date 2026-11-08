module

public import ArtGallery.Orthogonal.BoundaryPoint.ShaftPortal
public import Mathlib.Tactic.Linarith

/-! # Localization by perpendicular shaft and cap pockets

In the chart of a role, the shaft tips force the tangent coordinate into
[l,r]. The single cap tip confines the normal coordinate to a one-sided
thin strip. If the polygon boundary has clearance on that side, every
boundary guard seeing all three witnesses belongs to the designated spot.
-/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PerpendicularPin
open Set

structure Frame where
  swap : Bool
  negT : Bool
  negN : Bool

def Frame.pt (f : Frame) (p : Point) : Point :=
  let a := if f.swap then p.2 else p.1
  let b := if f.swap then p.1 else p.2
  (if f.negT then -a else a,if f.negN then -b else b)

theorem Frame.segment {q a b : Point} (f : Frame) (h : q ∈ ArtGallery.segment a b) :
    f.pt q ∈ ArtGallery.segment (f.pt a) (f.pt b) := by
  obtain ⟨s,hs,hs',rfl⟩ := h
  refine ⟨s,hs,hs',?_⟩
  rcases f with ⟨c,d,e⟩
  cases c <;> cases d <;> cases e <;> ext <;> simp [Frame.pt] <;> ring

private theorem at_portal {P : Polygon} {F R : Set Point} {g w : Point}
    (hc : IsClosed F) (hr : IsClosed R) (hfill : P.filled=F ∪ R)
    (hw : w ∈ F) (hg : g ∈ R) (hsee : P.Sees g w) :
    ∃ q ∈ ArtGallery.segment w g, q ∈ F ∩ R := by
  apply SingleWindow.segment_meets_window hc hr hw hg
  simpa only [Polygon.Sees,Geometry.segment_comm w g,← hfill] using hsee

/-- The first two witnesses alone determine the tangent-coordinate strip.
The proof allows a guard inside the shaft or outside it. -/
theorem tangent {P : Polygon} {F R : Set Point} {g w₀ w₁ : Point} {f : Frame}
    {l r nearH farH : ℝ} (hne : nearH≠farH)
    (hc : IsClosed F) (hr : IsClosed R) (hfill : P.filled=F ∪ R)
    (hshaft : ∀ q ∈ F, l≤(f.pt q).1 ∧ (f.pt q).1≤r)
    (hdoor : ∀ q ∈ F ∩ R, (f.pt q).2=nearH)
    (h₀ : w₀ ∈ F) (h₁ : w₁ ∈ F) (hw₀ : f.pt w₀=(l,farH)) (hw₁ : f.pt w₁=(r,farH))
    (hg : g ∈ P.filled) (hsee₀ : P.Sees g w₀) (hsee₁ : P.Sees g w₁) :
    l≤(f.pt g).1 ∧ (f.pt g).1≤r := by
  rw [hfill] at hg
  rcases hg with h|h
  · exact hshaft g h
  have param (w : Point) (x : ℝ) (hW : w∈F) (hw : f.pt w=(x,farH)) (hs : P.Sees g w) :
      ∃ s : ℝ, 0<s ∧ l≤x+s*((f.pt g).1-x) ∧ x+s*((f.pt g).1-x)≤r := by
    obtain ⟨q,hq,hqr⟩ := at_portal hc hr hfill hW h hs
    have hm := f.segment hq
    rw [hw] at hm
    obtain ⟨s,hs₀,_,he⟩ := hm
    have ht := congrArg Prod.fst he
    have hn := congrArg Prod.snd he
    change (f.pt q).1=x+s*((f.pt g).1-x) at ht
    change (f.pt q).2=farH+s*((f.pt g).2-farH) at hn
    rw [hdoor q hqr] at hn
    have hp : 0<s := lt_of_le_of_ne hs₀ (fun e => by subst s; exact hne (by simpa using hn))
    exact ⟨s,hp,ht ▸ (hshaft q hqr.1)⟩
  obtain ⟨s,hs,hl,_⟩ := param w₀ l h₀ hw₀ hsee₀
  obtain ⟨t,ht,_,hu⟩ := param w₁ r h₁ hw₁ hsee₁
  constructor
  · by_contra! hn
    linarith [mul_neg_of_pos_of_neg hs (sub_neg.mpr hn)]
  · by_contra! hn
    linarith [mul_pos ht (sub_pos.mpr hn)]

/-- The cap reaches in the positive tangent direction and its normal
interval starts at h. The guard is known to lie beyond the cap. -/
theorem normal_bound {P : Polygon} {C R : Set Point} {g w : Point} {f : Frame}
    {c face h top r : ℝ} (hdepth : c<face)
    (hc : IsClosed C) (hr : IsClosed R) (hfill : P.filled=C ∪ R)
    (hdoor : ∀ q ∈ C ∩ R, (f.pt q).1=face ∧ h≤(f.pt q).2 ∧ (f.pt q).2≤top)
    (hw : w∈C) (hcoords : f.pt w=(c,h)) (hg : g∈R) (hsee : P.Sees g w)
    (hwidth : (f.pt g).1≤r) :
    h≤(f.pt g).2 ∧ ((f.pt g).2-h)*(face-c)≤(r-c)*(top-h) := by
  obtain ⟨q,hq,hqr⟩ := at_portal hc hr hfill hw hg hsee
  obtain ⟨ht,hn,hu⟩ := hdoor q hqr
  have hm := f.segment hq
  rw [hcoords] at hm
  obtain ⟨s,hs,_,he⟩ := hm
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change (f.pt q).1=c+s*((f.pt g).1-c) at hx
  change (f.pt q).2=h+s*((f.pt g).2-h) at hy
  rw [ht] at hx
  have hp : 0<s := by
    rcases hs.eq_or_lt with hzero|hpos
    · subst s; simp at hx; linarith
    · exact hpos
  have hgt : 0≤(f.pt g).1-c := by
    by_contra! hh
    linarith [mul_neg_of_pos_of_neg hp hh]
  constructor
  · by_contra! hh
    linarith [mul_neg_of_pos_of_neg hp (sub_neg.mpr hh)]
  · calc
      ((f.pt g).2-h)*(face-c) = (s*((f.pt g).2-h))*((f.pt g).1-c) := by rw [hx]; ring
      _ ≤ (top-h)*((f.pt g).1-c) := mul_le_mul_of_nonneg_right (by linarith) hgt
      _ ≤ (r-c)*(top-h) := by rw [mul_comm (r-c)]; exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-- Clearance to the next possible boundary height forces equality, even
for a point on the closed extremal side of the permitted strip. -/
theorem force_level {y h limit depth reach thickness : ℝ}
    (hd : 0<depth) (hs : h≤y) (hc : y=h ∨ limit≤y)
    (hb : (y-h)*depth≤reach*thickness) (hgap : reach*thickness<(limit-h)*depth) : y=h := by
  rcases hc with he | hle
  · exact he
  · have := mul_le_mul_of_nonneg_right (sub_le_sub_right hle h) hd.le
    linarith

end ArtGallery.Orthogonal.BoundaryPoint.PerpendicularPin
end
