module

public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Chart
public import ArtGallery.Orthogonal.BoundaryPoint.CopySpec
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRecords
public import ArtGallery.Orthogonal.BoundaryPoint.WingModel
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.CopyInc.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.CopyMatch.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.Lower_10_40_1000

/-! The chart and role records of profile `Lower_10_40_1000` for its nook copy tests (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.Lower_10_40_1000
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert CellCert CellRoles CopyChannel SpanCells RoomCoordinates ArtGallery.Orthogonal.Hard
open WingOrder.Lower_10_40_1000
set_option maxRecDepth 200000
set_option maxHeartbeats 0

abbrev C : Chart := SepWing.chartOf template cache boxes WingRecords.Lower_10_40_1000.index

theorem C_lit : C=SepData.Lower_10_40_1000.Chart.CL := SepData.Lower_10_40_1000.Chart.C_eq

/-- The emitted role records are the index data on the chart grid. -/
theorem records : CopySpec.Records template WingRecords.Lower_10_40_1000.index 3 := by
  unfold CopySpec.Records
  intro rs size n j hn hj hr s args
  obtain ⟨-,-,eq⟩ := WingModel.good_at_size (t:=template) (size ▸ WingBounds.Lower_10_40_1000.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,WingRecords.Lower_10_40_1000.records⟩
    (fun g hx hy => WingChart.Lower_10_40_1000.simple g hx hy) SepData.Lower_10_40_1000.cert (WingFill.Lower_10_40_1000.filled_eq size n j hn hj hr)
  exact CopyRecords.of_join eq

end ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.Lower_10_40_1000
end
