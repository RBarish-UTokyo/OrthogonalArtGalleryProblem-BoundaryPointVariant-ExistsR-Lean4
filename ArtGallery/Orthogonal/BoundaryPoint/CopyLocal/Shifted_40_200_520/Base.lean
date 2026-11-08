module

public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Shifted_40_200_520.Chart
public import ArtGallery.Orthogonal.BoundaryPoint.CopySpec
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRecords
public import ArtGallery.Orthogonal.BoundaryPoint.WingModel
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.CopyInc.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.CopyMatch.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.Shifted_40_200_520

/-! The chart and role records of profile `Shifted_40_200_520` for its nook copy tests (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.Shifted_40_200_520
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert CellCert CellRoles CopyChannel SpanCells RoomCoordinates ArtGallery.Orthogonal.Hard
open WingOrder.Shifted_40_200_520
set_option maxRecDepth 200000
set_option maxHeartbeats 0

abbrev C : Chart := SepWing.chartOf template cache boxes WingRecords.Shifted_40_200_520.index

theorem C_lit : C=SepData.Shifted_40_200_520.Chart.CL := SepData.Shifted_40_200_520.Chart.C_eq

/-- The emitted role records are the index data on the chart grid. -/
theorem records : CopySpec.Records template WingRecords.Shifted_40_200_520.index 3 := by
  unfold CopySpec.Records
  intro rs size n j hn hj hr s args
  obtain ⟨-,-,eq⟩ := WingModel.good_at_size (t:=template) (size ▸ WingBounds.Shifted_40_200_520.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,WingRecords.Shifted_40_200_520.records⟩
    (fun g hx hy => WingChart.Shifted_40_200_520.simple g hx hy) SepData.Shifted_40_200_520.cert (WingFill.Shifted_40_200_520.filled_eq size n j hn hj hr)
  exact CopyRecords.of_join eq

end ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.Shifted_40_200_520
end
