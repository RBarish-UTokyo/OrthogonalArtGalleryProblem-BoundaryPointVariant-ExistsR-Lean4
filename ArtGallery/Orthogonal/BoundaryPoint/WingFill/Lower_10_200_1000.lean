module

public import ArtGallery.Orthogonal.BoundaryPoint.WingTiles
public import ArtGallery.Orthogonal.BoundaryPoint.WingRecords.Lower_10_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.Lower_10_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.Lower_40_200_1000

/-! Closed filled region of the emitted wing in its local coordinates. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingFill.Lower_10_200_1000
open GridSweep WingOrder.Lower_10_200_1000 WingRecords.Lower_10_200_1000
set_option maxRecDepth 16000
set_option maxHeartbeats 16000000

theorem sweep : Checked template.chart.cycle.points index.1 template.chart.y.length 0 (2*template.chart.x.length+1) :=
  ArtGallery.Orthogonal.BoundaryPoint.WingFill.Lower_40_200_1000.sweep

theorem filled_eq {ranks : List Nat} (size : ranks.length=3) (n j : Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈ranks,i≤n) :
    let s := (1:ℚ)/n
    WingTiles.Filled template (s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)) :=
  WingTiles.at_size (size ▸ CertifiedWing.Lower_10_200_1000.evidence) n j hn hj hr index
    ⟨sizes,verified,x_ok,y_ok,records⟩ WingChart.Lower_10_200_1000.axis_edges cell_indices sweep

end ArtGallery.Orthogonal.BoundaryPoint.WingFill.Lower_10_200_1000
end
