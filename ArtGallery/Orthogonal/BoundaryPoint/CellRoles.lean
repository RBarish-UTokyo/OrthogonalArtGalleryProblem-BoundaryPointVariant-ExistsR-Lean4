module

public import ArtGallery.Orthogonal.BoundaryPoint.CellCert

/-! # Exclusion of every other role of a wing from a target cell

A list of cell certificates, one per role of the wing (none for the receiver),
excludes every point of every other role's spot from seeing the open target
cell inside the chart polygon. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CellRoles
open SepCert CellCert SpanCells GridAtom GridParity RoomGrid SepGeom ArtGallery.Orthogonal.Hard

/-- A cell certificate for one guard segment. -/
inductive CellEx
  | cross (k : Nat) (pos : Bool) (qs : List Quad)
  | half (k : Nat)

def CellEx.ok (C : Chart) (g₀ g₁ : Index) (cell : Nat × Nat) : CellEx → Bool
  | .cross k pos qs => CellCert.cross C g₀ g₁ cell k pos qs
  | .half k => CellCert.half C g₀ g₁ cell k

/-- The spot of a role record: its second and third nodes. -/
def spotA (r : List Index) : Index := r.getD 1 (0,0)
def spotB (r : List Index) : Index := r.getD 2 (0,0)

/-- Every role except the receiver `rr` carries a valid certificate. -/
def allOK (C : Chart) (cell : Nat × Nat) (rr : Nat) : Nat → List (List Index) → List (Option CellEx) → Bool
  | _,[],[] => true
  | i,r::rs,e::es => (if i=rr then true else match e with
      | some e => e.ok C (spotA r) (spotB r) cell
      | none => false) && allOK C cell rr (i+1) rs es
  | _,_,_ => false

/-- Checking along a split of the role list. -/
theorem allOK_split {C : Chart} {cell : Nat × Nat} {rr : Nat} : ∀ (n i : Nat) (rs : List (List Index)) (es : List (Option CellEx)),
    allOK C cell rr i (rs.take n) (es.take n)=true → allOK C cell rr (i+n) (rs.drop n) (es.drop n)=true →
      allOK C cell rr i rs es=true
  | 0,i,rs,es,_,h => by simpa using h
  | n+1,i,[],[],_,_ => rfl
  | n+1,i,r::rs,e::es,h1,h2 => by
    simp only [List.take_succ_cons,allOK,Bool.and_eq_true] at h1 ⊢
    exact ⟨h1.1,allOK_split n (i+1) rs es h1.2 (by simpa [Nat.add_assoc,Nat.add_comm 1 n] using h2)⟩
  | n+1,i,_::_,[],h1,_ => by simp [allOK] at h1
  | n+1,i,[],_::_,h1,_ => by simp [allOK] at h1

theorem allOK_get {C : Chart} {cell : Nat × Nat} {rr : Nat} :
    ∀ {i : Nat} {rs : List (List Index)} {es : List (Option CellEx)}, allOK C cell rr i rs es=true →
      ∀ j (hj : j<rs.length), i+j≠rr → ∃ e, es[j]?=some (some e) ∧ e.ok C (spotA rs[j]) (spotB rs[j]) cell=true
  | _,[],[],_ => by intro j hj; simp at hj
  | _,[],_::_,h => by simp [allOK] at h
  | _,_::_,[],h => by simp [allOK] at h
  | i,r::rs,e::es,h => by
    intro j hj ne
    simp only [allOK,Bool.and_eq_true] at h
    cases j with
    | zero =>
      simp only [Nat.add_zero] at ne
      simp only [ne,ite_false] at h
      cases e with
      | none => simp at h
      | some e => exact ⟨e,rfl,h.1⟩
    | succ j =>
      obtain ⟨e',h1,h2⟩ := allOK_get h.2 j (by simpa using hj) (by omega)
      exact ⟨e',by simpa using h1,by simpa using h2⟩

variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

theorem CellEx.sound (G : Good C X Y s A) {g₀ g₁ : Index} {cell : Nat × Nat} {e : CellEx}
    (h : e.ok C g₀ g₁ cell=true) (hc : Inner C.nx cell.1 ∧ Inner C.ny cell.2) {z : Point}
    (hz : z∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁)) {w : Point}
    (wx : atom w.1 X=cell.1) (wy : atom w.2 Y=cell.2) : ¬(C.poly X Y).Sees z w := by
  cases e with
  | cross k pos qs => exact cross_sound G h hz wx wy
  | half k => exact half_sound G h hc hz wx wy

/-- No point of another role's spot sees the open target cell inside the chart. -/
theorem others (G : Good C X Y s A) {cell : Nat × Nat} {rr : Nat} {rs : List (List Index)}
    {es : List (Option CellEx)} (h : allOK C cell rr 0 rs es=true) (hc : Inner C.nx cell.1 ∧ Inner C.ny cell.2)
    {j : Nat} (hj : j<rs.length) (ne : j≠rr) {z : Point}
    (hz : z∈ArtGallery.segment (gridPt X Y (spotA rs[j])) (gridPt X Y (spotB rs[j]))) {w : Point}
    (wx : atom w.1 X=cell.1) (wy : atom w.2 Y=cell.2) : ¬(C.poly X Y).Sees z w := by
  obtain ⟨e,-,he⟩ := allOK_get h j hj (by omega)
  exact e.sound G he hc hz wx wy

end ArtGallery.Orthogonal.BoundaryPoint.CellRoles
end
