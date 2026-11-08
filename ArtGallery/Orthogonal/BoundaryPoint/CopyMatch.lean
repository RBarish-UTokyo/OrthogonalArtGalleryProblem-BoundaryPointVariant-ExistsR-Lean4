module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyChannel
public import ArtGallery.Orthogonal.BoundaryPoint.RegCert
public import ArtGallery.Orthogonal.BoundaryPoint.IndexedWing

/-! # Matched rays from lifted polynomial identities

The two conditions `E0=0` and `E1=0` of `CopyChannel.matched_of` are checked on
polynomial lifts: every quantity `v` is a quotient `N/D`, a common denominator `L`
with `D*C=L` turns it into the polynomial `V=N*C=v*L`, and the homogeneous cubic
forms satisfy `E(V)=L^3*E(v)`. The lifted identities are certified by `KronCert`. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyMatch
open KronCert CopyChannel RoomCoordinates

/-- The parameter condition, homogenised by `one` and with `κ=2/3*(Sx-Rx)`. -/
def E1h (By cBy a Ry cRy Rx Sx one : ℝ) : ℝ :=
  3*(cBy-a)*(cRy-Ry)*one-2*(Sx-Rx)*(cRy-a)*(cBy-By)

/-- A quotient lifted to the common denominator. -/
theorem lifted {v N D C L : ℝ} (h : v*D=N) (hc : D*C=L) : N*C=v*L := by
  rw [←h,←hc]; ring

theorem matched_lift {Bx By cBx cBy a Rx Ry cRx cRy Sx L : ℝ} (hL : L≠0)
    (hB : cBy≠By) (hR : cRy≠Ry)
    (h0 : E0 (Bx*L) (By*L) (cBx*L) (cBy*L) (a*L) (Rx*L) (Ry*L) (cRx*L) (cRy*L)=0)
    (h1 : E1h (By*L) (cBy*L) (a*L) (Ry*L) (cRy*L) (Rx*L) (Sx*L) L=0) (t : ℝ) :
    lineX (Bx+t,By) (cBx,cBy) a=lineX (Rx+2/3*(Sx-Rx)*t,Ry) (cRx,cRy) a := by
  have hL3 : L^3≠0 := pow_ne_zero 3 hL
  have e0 : E0 Bx By cBx cBy a Rx Ry cRx cRy=0 := by
    have : L^3*E0 Bx By cBx cBy a Rx Ry cRx cRy=0 := by rw [←h0]; unfold E0; ring
    exact (mul_eq_zero.mp this).resolve_left hL3
  have e1 : E1 By cBy a Ry cRy (2/3*(Sx-Rx))=0 := by
    have : 3*L^3*E1 By cBy a Ry cRy (2/3*(Sx-Rx))=0 := by rw [←h1]; unfold E1 E1h; ring
    rcases mul_eq_zero.mp this with h|h
    · exact absurd h (mul_ne_zero three_ne_zero hL3)
    · exact h
  exact matched_of hB hR e0 e1 t

/-! ## Expression trees of the two lifted forms -/

def E0x (Bx By cBx cBy a Rx Ry cRx cRy : Ex) : Ex :=
  .sub (.mul (.add (.mul Bx (.sub cBy By)) (.mul (.sub cBx Bx) (.sub a By))) (.sub cRy Ry))
    (.mul (.add (.mul Rx (.sub cRy Ry)) (.mul (.sub cRx Rx) (.sub a Ry))) (.sub cBy By))

def E1x (By cBy a Ry cRy Rx Sx one : Ex) : Ex :=
  .sub (.mul (.mul (.mul (.lit [[[3]]]) (.sub cBy a)) (.sub cRy Ry)) one)
    (.mul (.mul (.mul (.lit [[[2]]]) (.sub Sx Rx)) (.sub cRy a)) (.sub cBy By))

theorem E0x_ev (x y z : ℝ) (Bx By cBx cBy a Rx Ry cRx cRy : Ex) :
    (E0x Bx By cBx cBy a Rx Ry cRx cRy).ev x y z=E0 (Bx.ev x y z) (By.ev x y z) (cBx.ev x y z)
      (cBy.ev x y z) (a.ev x y z) (Rx.ev x y z) (Ry.ev x y z) (cRx.ev x y z) (cRy.ev x y z) := by
  simp only [E0x,Ex.ev,E0]

theorem E1x_ev (x y z : ℝ) (By cBy a Ry cRy Rx Sx one : Ex) :
    (E1x By cBy a Ry cRy Rx Sx one).ev x y z=E1h (By.ev x y z) (cBy.ev x y z) (a.ev x y z)
      (Ry.ev x y z) (cRy.ev x y z) (Rx.ev x y z) (Sx.ev x y z) (one.ev x y z) := by
  simp only [E1x,Ex.ev,E1h,ev3,ev2,ev1]; push_cast; ring

/-- A lifted quantity: `v*D=N` and `D*C=L` give `N*C=v*L`. -/
structure Lift (x y z v : ℝ) (L N D C : Ex) : Prop where
  quot : v*D.ev x y z=N.ev x y z
  cof : RegCert.auto (.sub (.mul D C) L)=true

theorem Lift.eq {x y z v : ℝ} {L N D C : Ex} (h : Lift x y z v L N D C) :
    (Ex.mul N C).ev x y z=v*L.ev x y z := by
  have c := Ex.sound h.cof x y z
  simp only [Ex.ev] at c ⊢
  exact lifted h.quot (sub_eq_zero.mp c)

/-- Matched rays from ten lifted quantities and two Kronecker checks. -/
theorem matched {x y z : ℝ} {L : Ex} (hL : L.ev x y z≠0)
    {Bx By cBx cBy a Rx Ry cRx cRy Sx : ℝ} {N0 D0 C0 N1 D1 C1 N2 D2 C2 N3 D3 C3 N4 D4 C4
      N5 D5 C5 N6 D6 C6 N7 D7 C7 N8 D8 C8 N9 D9 C9 : Ex}
    (lBx : Lift x y z Bx L N0 D0 C0) (lBy : Lift x y z By L N1 D1 C1)
    (lcBx : Lift x y z cBx L N2 D2 C2) (lcBy : Lift x y z cBy L N3 D3 C3)
    (la : Lift x y z a L N4 D4 C4) (lRx : Lift x y z Rx L N5 D5 C5) (lRy : Lift x y z Ry L N6 D6 C6)
    (lcRx : Lift x y z cRx L N7 D7 C7) (lcRy : Lift x y z cRy L N8 D8 C8) (lSx : Lift x y z Sx L N9 D9 C9)
    (k0 : RegCert.auto (E0x (.mul N0 C0) (.mul N1 C1) (.mul N2 C2) (.mul N3 C3) (.mul N4 C4) (.mul N5 C5)
      (.mul N6 C6) (.mul N7 C7) (.mul N8 C8))=true)
    (k1 : RegCert.auto (E1x (.mul N1 C1) (.mul N3 C3) (.mul N4 C4) (.mul N6 C6) (.mul N8 C8) (.mul N5 C5)
      (.mul N9 C9) L)=true)
    (hB : cBy≠By) (hR : cRy≠Ry) (t : ℝ) :
    lineX (Bx+t,By) (cBx,cBy) a=lineX (Rx+2/3*(Sx-Rx)*t,Ry) (cRx,cRy) a := by
  have h0 := Ex.sound k0 x y z
  have h1 := Ex.sound k1 x y z
  rw [E0x_ev] at h0; rw [E1x_ev] at h1
  simp only [lBx.eq,lBy.eq,lcBx.eq,lcBy.eq,la.eq,lRx.eq,lRy.eq,lcRx.eq,lcRy.eq,lSx.eq] at h0 h1
  exact matched_lift hL hB hR h0 h1 t

/-! ## Room levels in closed form -/

theorem positions_getD {α : Type} [AddCommMonoid α] (f : Gap → α) :
    ∀ (gs : List Gap) (z : α) (l : Nat), l≤gs.length →
      (positions f z gs).getD l 0=z+((gs.take l).map f).sum
  | [],z,l,h => by simp at h; subst h; simp [positions]
  | g::gs,z,0,_ => by simp [positions]
  | g::gs,z,l+1,h => by
      simp only [positions,List.getD_cons_succ,List.take_succ_cons,List.map_cons,List.sum_cons]
      rw [positions_getD f gs (z+f g) l (by simpa using h),add_assoc]

theorem level_cast (a : Axis) (s : ℚ) (l : Nat) :
    (((a.coordsQ s).getD l 0 : ℚ) : ℝ)=(a.coordsR (s:ℝ)).getD l 0 := by
  rw [←cast_coords]; simp [List.getD_eq_getElem?_getD]
  cases (a.coordsQ s)[l]? <;> simp

theorem level_eq (a : Axis) (s : ℝ) (l : Nat) (h : l≤a.gaps.length) :
    (a.coordsR s).getD l 0=evalR s a.initial+((a.gaps.take l).map fun g => g.valR s).sum :=
  positions_getD _ a.gaps _ l h

/-! ## Chart grid values -/

open IndexedWing ShapeRefs RegisterOrder MarginCert in
theorem grid_ref {t : ChartDrawing.Template} {args xs rs bs cache} (m : Model args xs rs bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) (y : Bool) (i : Nat) :
    ((grid t args y).map (fun q : ℚ => (q:ℝ))).getD i 0=
      ((readRef xs (axisOf t y) (MarginCert.getRat args 0) ((refsFor t y).getD i 0) : ℚ) : ℝ) := by
  rw [←grid_value m run y i]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases (grid t args y)[i]? <;> simp

end ArtGallery.Orthogonal.BoundaryPoint.CopyMatch
end
