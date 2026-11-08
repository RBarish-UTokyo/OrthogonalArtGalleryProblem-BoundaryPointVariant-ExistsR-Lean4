module

public import ArtGallery.Orthogonal.BoundaryPoint.WingTiles
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.InvLe_1_200

/-! Closed filled region of the emitted wing in its local coordinates. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingFill.InvLe_40_200
open GridSweep WingOrder.InvLe_40_200 WingRecords.InvLe_40_200
set_option maxRecDepth 16000
set_option maxHeartbeats 16000000

theorem sweep : Checked template.chart.cycle.points index.1 template.chart.y.length 0 (2*template.chart.x.length+1) :=
  ArtGallery.Orthogonal.BoundaryPoint.WingFill.InvLe_1_200.sweep

theorem filled_eq {ranks : List Nat} (size : ranks.length=2) (n j : Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈ranks,i≤n) :
    let s := (1:ℚ)/n
    WingTiles.Filled template (s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)) :=
  WingTiles.at_size (size ▸ CertifiedWing.InvLe_40_200.evidence) n j hn hj hr index
    ⟨sizes,verified,x_ok,y_ok,records⟩ WingChart.InvLe_40_200.axis_edges cell_indices sweep

end ArtGallery.Orthogonal.BoundaryPoint.WingFill.InvLe_40_200
end
