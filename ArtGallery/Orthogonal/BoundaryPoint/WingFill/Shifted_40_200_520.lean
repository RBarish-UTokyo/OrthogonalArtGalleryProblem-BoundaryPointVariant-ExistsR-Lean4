module

public import ArtGallery.Orthogonal.BoundaryPoint.WingTiles
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.Ordinary_40_200_520

/-! Closed filled region of the emitted wing in its local coordinates. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingFill.Shifted_40_200_520
open GridSweep WingOrder.Shifted_40_200_520 WingRecords.Shifted_40_200_520
set_option maxRecDepth 16000
set_option maxHeartbeats 16000000

theorem sweep : Checked template.chart.cycle.points index.1 template.chart.y.length 0 (2*template.chart.x.length+1) :=
  ArtGallery.Orthogonal.BoundaryPoint.WingFill.Ordinary_40_200_520.sweep

theorem filled_eq {ranks : List Nat} (size : ranks.length=3) (n j : Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈ranks,i≤n) :
    let s := (1:ℚ)/n
    WingTiles.Filled template (s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)) :=
  WingTiles.at_size (size ▸ CertifiedWing.Shifted_40_200_520.evidence) n j hn hj hr index
    ⟨sizes,verified,x_ok,y_ok,records⟩ WingChart.Shifted_40_200_520.axis_edges cell_indices sweep

end ArtGallery.Orthogonal.BoundaryPoint.WingFill.Shifted_40_200_520
end
