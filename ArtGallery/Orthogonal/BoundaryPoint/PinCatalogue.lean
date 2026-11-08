module

public import ArtGallery.Orthogonal.BoundaryPoint.PinTransport
public import ArtGallery.Orthogonal.BoundaryPoint.WingGates.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingPins.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingGates.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingPins.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingGates.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingPins.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingGates.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingPins.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingGates.Lower_10_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingPins.Lower_10_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingGates.Lower_10_360_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingPins.Lower_10_360_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingGates.Lower_10_520_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingPins.Lower_10_520_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingGates.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.WingPins.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.WingGates.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingPins.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingGates.InvLe_1_360
public import ArtGallery.Orthogonal.BoundaryPoint.WingPins.InvLe_1_360
public import ArtGallery.Orthogonal.BoundaryPoint.WingGates.InvLe_1_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingPins.InvLe_1_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingGates.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.WingPins.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.WingGates.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingPins.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingGates.InvRevGe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingPins.InvRevGe_40_200

/-! Local three-witness forcing and one closed-door exclusion per generated role. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PinCatalogue
open ChartDrawing WingPinProof WingEscape WingMarks

def Profile (t : Template) (arity : Nat) : Prop := ∀ (rs : List Nat),rs.length=arity →
  ∀ n j : Nat,65≤n → j≤n → (∀ i∈rs,i≤n) →
    let s := (1:ℚ)/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    Holds t args ∧ Hidden t args ∧ Forces t args

theorem catalogue : List.Forall₂ Profile catalog WingSeparation.arities := by
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.Ordinary_40_200_520.on_boundary h n j hn hj hr,
    WingGates.Ordinary_40_200_520.hidden h n j hn hj hr,WingPins.Ordinary_40_200_520.localized h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.Shifted_40_200_520.on_boundary h n j hn hj hr,
    WingGates.Shifted_40_200_520.hidden h n j hn hj hr,WingPins.Shifted_40_200_520.localized h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.Lower_40_200_1000.on_boundary h n j hn hj hr,
    WingGates.Lower_40_200_1000.hidden h n j hn hj hr,WingPins.Lower_40_200_1000.localized h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.Lower_10_40_1000.on_boundary h n j hn hj hr,
    WingGates.Lower_10_40_1000.hidden h n j hn hj hr,WingPins.Lower_10_40_1000.localized h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.Lower_10_200_1000.on_boundary h n j hn hj hr,
    WingGates.Lower_10_200_1000.hidden h n j hn hj hr,WingPins.Lower_10_200_1000.localized h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.Lower_10_360_1000.on_boundary h n j hn hj hr,
    WingGates.Lower_10_360_1000.hidden h n j hn hj hr,WingPins.Lower_10_360_1000.localized h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.Lower_10_520_1000.on_boundary h n j hn hj hr,
    WingGates.Lower_10_520_1000.hidden h n j hn hj hr,WingPins.Lower_10_520_1000.localized h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.InvLe_1_40.on_boundary h n j hn hj hr,
    WingGates.InvLe_1_40.hidden h n j hn hj hr,WingPins.InvLe_1_40.localized h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.InvLe_1_200.on_boundary h n j hn hj hr,
    WingGates.InvLe_1_200.hidden h n j hn hj hr,WingPins.InvLe_1_200.localized h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.InvLe_1_360.on_boundary h n j hn hj hr,
    WingGates.InvLe_1_360.hidden h n j hn hj hr,WingPins.InvLe_1_360.localized h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.InvLe_1_520.on_boundary h n j hn hj hr,
    WingGates.InvLe_1_520.hidden h n j hn hj hr,WingPins.InvLe_1_520.localized h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.InvRevGe_1_10.on_boundary h n j hn hj hr,
    WingGates.InvRevGe_1_10.hidden h n j hn hj hr,WingPins.InvRevGe_1_10.localized h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.InvLe_40_200.on_boundary h n j hn hj hr,
    WingGates.InvLe_40_200.hidden h n j hn hj hr,WingPins.InvLe_40_200.localized h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.InvRevGe_40_200.on_boundary h n j hn hj hr,
    WingGates.InvRevGe_40_200.hidden h n j hn hj hr,WingPins.InvRevGe_40_200.localized h n j hn hj hr⟩)
  exact List.Forall₂.nil

end ArtGallery.Orthogonal.BoundaryPoint.PinCatalogue
end
