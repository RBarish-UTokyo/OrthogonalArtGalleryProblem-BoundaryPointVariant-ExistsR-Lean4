module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRoles
public import ArtGallery.Orthogonal.BoundaryPoint.CopyMatch
public import ArtGallery.Orthogonal.BoundaryPoint.GlobalPins

/-! # The copy test of one channel in a wing's local frame

`Test t idx arity qk bank ra rb rr up` says: at every admissible size, in any
polygon joined to the chart along the door, with a guard cover, a base guard on
the floor at offset `tB` (or blind to the wing), the receiver at parameter `tR` on
its spot `[ra,rb]`, and every other guard either on another role's spot of the
wing or blind to the copy targets, the copy inequality holds: `tB ≤ tR` (nook
test) or `tR ≤ tB` (chamber test, `up`). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopySpec
open ChartDrawing BoundaryChart IndexedWing MarginCert SepCert CellRoles CopyRoles RoomGrid CorridorProgram GridAtom ArtGallery.Orthogonal.Hard

def dir : Bool → ℝ → ℝ → Prop
  | true,tB,tR => tR≤tB
  | false,tB,tR => tB≤tR

def Test (t : Template) (idx : Data Nat) (arity qk bank : Nat) (ra rb : Index) (rr : Nat) (up : Bool) : Prop :=
  ∀ {rs : List Nat}, rs.length=arity → ∀ n j : Nat, 65≤n → j≤n → (∀ i∈rs,i≤n) →
    let s : ℚ := 1/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    let X := (grid t args false).map (fun q : ℚ => (q:ℝ))
    let Y := (grid t args true).map (fun q : ℚ => (q:ℝ))
    let sr : ℝ := s
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args qk
    let b : ℝ := (((bank:ℝ)-1/5)/1001+5/2002*Q+40/1001*J*sr : ℝ)
    let D : ℝ := 50050/sr^2
    let W : ℝ := sr/320
    let L := (actual t.chart (ShapeRefs.join (t.corridor.coords args) (t.room.coords s))).filled
    ∀ {P : Polygon} {rest : Set Point}, P.filled=L∪rest → IsClosed rest → L∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1) →
    ∀ {Gs : Finset Point}, (∀ z∈P.filled, ∃ g∈Gs, P.Sees g z) →
    ∀ {tB tR : ℝ} {Bg : Point}, (0≤tB ∧ tB≤3/2) → (0≤tR ∧ tR≤3/2) →
    ((Bg=(W+b*D+tB,1-D) ∧ Bg∈rest) ∨ ∀ z∈L, ¬P.Sees Bg z) →
    CopyLower.receiver X Y ra rb tR∈L →
    (∀ g∈Gs, g≠Bg → g≠CopyLower.receiver X Y ra rb tR →
      (∃ k, ∃ hk : k < idx.2.length, k≠rr ∧
        g∈ArtGallery.segment (gridPt X Y (spotA idx.2[k])) (gridPt X Y (spotB idx.2[k])) ∧ g∈L) ∨
      Blind P L W b D g) →
    dir up tB tR

/-- The emitted role records of a wing are its index data on the chart grid. -/
def Records (t : Template) (idx : Data Nat) (arity : Nat) : Prop :=
  ∀ {rs : List Nat}, rs.length=arity → ∀ n j : Nat, 65≤n → j≤n → (∀ i∈rs,i≤n) →
    let s : ℚ := 1/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    GlobalPins.records t n j rs=idx.2.map (fun l => l.map fun p => ((grid t args false).getD p.1 0,(grid t args true).getD p.2 0))

end ArtGallery.Orthogonal.BoundaryPoint.CopySpec
end
