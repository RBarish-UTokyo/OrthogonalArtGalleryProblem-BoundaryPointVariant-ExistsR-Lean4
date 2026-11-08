module

public import ArtGallery.Orthogonal.BoundaryPoint.PlacedMarks
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.Lower_10_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.Lower_10_360_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.Lower_10_520_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.InvLe_1_360
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.InvLe_1_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.InvRevGe_40_200

/-! Off-door boundary certificates for the fourteen fixed profiles. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingMarkCatalogue
open ChartDrawing PlacedMarks WingEnvelopeCert WingMarks MarginCert
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

def Safe (t : Template) (arity : Nat) : Prop := ∀ (rs : List Nat),rs.length=arity →
  ∀ n j : Nat,65≤n → j≤n → (∀ i∈rs,i≤n) →
    let s := (1:ℚ)/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    Holds t args ∧ Away t args

section
open WingOrder.Ordinary_40_200_520

theorem clear0 : PlacedMarks.check template boxes cache=true := by decide +kernel
theorem safe0 : Safe template 3 := by
  intro rs size n j hn hj hr; refine ⟨WingRecords.Ordinary_40_200_520.on_boundary size n j hn hj hr,?_⟩
  exact away_at_size (size ▸ WingBounds.Ordinary_40_200_520.certificate) n j hn hj hr cache ⟨sizes,verified,clear0⟩
end

section
open WingOrder.Shifted_40_200_520

theorem clear1 : PlacedMarks.check template boxes cache=true := by decide +kernel
theorem safe1 : Safe template 3 := by
  intro rs size n j hn hj hr; refine ⟨WingRecords.Shifted_40_200_520.on_boundary size n j hn hj hr,?_⟩
  exact away_at_size (size ▸ WingBounds.Shifted_40_200_520.certificate) n j hn hj hr cache ⟨sizes,verified,clear1⟩
end

section
open WingOrder.Lower_40_200_1000

theorem clear2 : PlacedMarks.check template boxes cache=true := by decide +kernel
theorem safe2 : Safe template 3 := by
  intro rs size n j hn hj hr; refine ⟨WingRecords.Lower_40_200_1000.on_boundary size n j hn hj hr,?_⟩
  exact away_at_size (size ▸ WingBounds.Lower_40_200_1000.certificate) n j hn hj hr cache ⟨sizes,verified,clear2⟩
end

section
open WingOrder.Lower_10_40_1000

theorem clear3 : PlacedMarks.check template boxes cache=true := by decide +kernel
theorem safe3 : Safe template 3 := by
  intro rs size n j hn hj hr; refine ⟨WingRecords.Lower_10_40_1000.on_boundary size n j hn hj hr,?_⟩
  exact away_at_size (size ▸ WingBounds.Lower_10_40_1000.certificate) n j hn hj hr cache ⟨sizes,verified,clear3⟩
end

section
open WingOrder.Lower_10_200_1000

theorem clear4 : PlacedMarks.check template boxes cache=true := by decide +kernel
theorem safe4 : Safe template 3 := by
  intro rs size n j hn hj hr; refine ⟨WingRecords.Lower_10_200_1000.on_boundary size n j hn hj hr,?_⟩
  exact away_at_size (size ▸ WingBounds.Lower_10_200_1000.certificate) n j hn hj hr cache ⟨sizes,verified,clear4⟩
end

section
open WingOrder.Lower_10_360_1000

theorem clear5 : PlacedMarks.check template boxes cache=true := by decide +kernel
theorem safe5 : Safe template 3 := by
  intro rs size n j hn hj hr; refine ⟨WingRecords.Lower_10_360_1000.on_boundary size n j hn hj hr,?_⟩
  exact away_at_size (size ▸ WingBounds.Lower_10_360_1000.certificate) n j hn hj hr cache ⟨sizes,verified,clear5⟩
end

section
open WingOrder.Lower_10_520_1000

theorem clear6 : PlacedMarks.check template boxes cache=true := by decide +kernel
theorem safe6 : Safe template 3 := by
  intro rs size n j hn hj hr; refine ⟨WingRecords.Lower_10_520_1000.on_boundary size n j hn hj hr,?_⟩
  exact away_at_size (size ▸ WingBounds.Lower_10_520_1000.certificate) n j hn hj hr cache ⟨sizes,verified,clear6⟩
end

section
open WingOrder.InvLe_1_40

theorem clear7 : PlacedMarks.check template boxes cache=true := by decide +kernel
theorem safe7 : Safe template 2 := by
  intro rs size n j hn hj hr; refine ⟨WingRecords.InvLe_1_40.on_boundary size n j hn hj hr,?_⟩
  exact away_at_size (size ▸ WingBounds.InvLe_1_40.certificate) n j hn hj hr cache ⟨sizes,verified,clear7⟩
end

section
open WingOrder.InvLe_1_200

theorem clear8 : PlacedMarks.check template boxes cache=true := by decide +kernel
theorem safe8 : Safe template 2 := by
  intro rs size n j hn hj hr; refine ⟨WingRecords.InvLe_1_200.on_boundary size n j hn hj hr,?_⟩
  exact away_at_size (size ▸ WingBounds.InvLe_1_200.certificate) n j hn hj hr cache ⟨sizes,verified,clear8⟩
end

section
open WingOrder.InvLe_1_360

theorem clear9 : PlacedMarks.check template boxes cache=true := by decide +kernel
theorem safe9 : Safe template 2 := by
  intro rs size n j hn hj hr; refine ⟨WingRecords.InvLe_1_360.on_boundary size n j hn hj hr,?_⟩
  exact away_at_size (size ▸ WingBounds.InvLe_1_360.certificate) n j hn hj hr cache ⟨sizes,verified,clear9⟩
end

section
open WingOrder.InvLe_1_520

theorem clear10 : PlacedMarks.check template boxes cache=true := by decide +kernel
theorem safe10 : Safe template 2 := by
  intro rs size n j hn hj hr; refine ⟨WingRecords.InvLe_1_520.on_boundary size n j hn hj hr,?_⟩
  exact away_at_size (size ▸ WingBounds.InvLe_1_520.certificate) n j hn hj hr cache ⟨sizes,verified,clear10⟩
end

section
open WingOrder.InvRevGe_1_10

theorem clear11 : PlacedMarks.check template boxes cache=true := by decide +kernel
theorem safe11 : Safe template 2 := by
  intro rs size n j hn hj hr; refine ⟨WingRecords.InvRevGe_1_10.on_boundary size n j hn hj hr,?_⟩
  exact away_at_size (size ▸ WingBounds.InvRevGe_1_10.certificate) n j hn hj hr cache ⟨sizes,verified,clear11⟩
end

section
open WingOrder.InvLe_40_200

theorem clear12 : PlacedMarks.check template boxes cache=true := by decide +kernel
theorem safe12 : Safe template 2 := by
  intro rs size n j hn hj hr; refine ⟨WingRecords.InvLe_40_200.on_boundary size n j hn hj hr,?_⟩
  exact away_at_size (size ▸ WingBounds.InvLe_40_200.certificate) n j hn hj hr cache ⟨sizes,verified,clear12⟩
end

section
open WingOrder.InvRevGe_40_200

theorem clear13 : PlacedMarks.check template boxes cache=true := by decide +kernel
theorem safe13 : Safe template 2 := by
  intro rs size n j hn hj hr; refine ⟨WingRecords.InvRevGe_40_200.on_boundary size n j hn hj hr,?_⟩
  exact away_at_size (size ▸ WingBounds.InvRevGe_40_200.certificate) n j hn hj hr cache ⟨sizes,verified,clear13⟩
end

theorem catalogue : List.Forall₂ Safe catalog WingSeparation.arities := by
  apply List.Forall₂.cons safe0
  apply List.Forall₂.cons safe1
  apply List.Forall₂.cons safe2
  apply List.Forall₂.cons safe3
  apply List.Forall₂.cons safe4
  apply List.Forall₂.cons safe5
  apply List.Forall₂.cons safe6
  apply List.Forall₂.cons safe7
  apply List.Forall₂.cons safe8
  apply List.Forall₂.cons safe9
  apply List.Forall₂.cons safe10
  apply List.Forall₂.cons safe11
  apply List.Forall₂.cons safe12
  apply List.Forall₂.cons safe13
  exact List.Forall₂.nil

end ArtGallery.Orthogonal.BoundaryPoint.WingMarkCatalogue
end
