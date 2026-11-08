module

public import ArtGallery.Orthogonal.BoundaryPoint.WingSeparation
public import ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.Lower_10_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.Lower_10_360_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.Lower_10_520_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.InvLe_1_360
public import ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.InvLe_1_520
public import ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.InvRevGe_40_200

/-! All 651 witness exclusions, parameterized by the actual input size and ranks. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PrivacyCatalogue
open ChartDrawing WingPrivacy WingMarks

def Profile (t : Template) (arity : Nat) : Prop := ∀ (rs : List Nat),rs.length=arity →
  ∀ n j : Nat,65≤n → j≤n → (∀ i∈rs,i≤n) →
    let s := (1:ℚ)/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    Holds t args ∧ AllHidden t args

theorem catalogue : List.Forall₂ Profile catalog WingSeparation.arities := by
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.Ordinary_40_200_520.on_boundary h n j hn hj hr,
    WitnessPrivacy.Ordinary_40_200_520.all_hidden h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.Shifted_40_200_520.on_boundary h n j hn hj hr,
    WitnessPrivacy.Shifted_40_200_520.all_hidden h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.Lower_40_200_1000.on_boundary h n j hn hj hr,
    WitnessPrivacy.Lower_40_200_1000.all_hidden h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.Lower_10_40_1000.on_boundary h n j hn hj hr,
    WitnessPrivacy.Lower_10_40_1000.all_hidden h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.Lower_10_200_1000.on_boundary h n j hn hj hr,
    WitnessPrivacy.Lower_10_200_1000.all_hidden h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.Lower_10_360_1000.on_boundary h n j hn hj hr,
    WitnessPrivacy.Lower_10_360_1000.all_hidden h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.Lower_10_520_1000.on_boundary h n j hn hj hr,
    WitnessPrivacy.Lower_10_520_1000.all_hidden h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.InvLe_1_40.on_boundary h n j hn hj hr,
    WitnessPrivacy.InvLe_1_40.all_hidden h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.InvLe_1_200.on_boundary h n j hn hj hr,
    WitnessPrivacy.InvLe_1_200.all_hidden h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.InvLe_1_360.on_boundary h n j hn hj hr,
    WitnessPrivacy.InvLe_1_360.all_hidden h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.InvLe_1_520.on_boundary h n j hn hj hr,
    WitnessPrivacy.InvLe_1_520.all_hidden h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.InvRevGe_1_10.on_boundary h n j hn hj hr,
    WitnessPrivacy.InvRevGe_1_10.all_hidden h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.InvLe_40_200.on_boundary h n j hn hj hr,
    WitnessPrivacy.InvLe_40_200.all_hidden h n j hn hj hr⟩)
  apply List.Forall₂.cons (fun rs h n j hn hj hr => ⟨WingRecords.InvRevGe_40_200.on_boundary h n j hn hj hr,
    WitnessPrivacy.InvRevGe_40_200.all_hidden h n j hn hj hr⟩)
  exact List.Forall₂.nil

end ArtGallery.Orthogonal.BoundaryPoint.PrivacyCatalogue
end
