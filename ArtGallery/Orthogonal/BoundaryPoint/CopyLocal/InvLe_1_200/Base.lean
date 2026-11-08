module

public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_1_200.Chart
public import ArtGallery.Orthogonal.BoundaryPoint.CopySpec
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRecords
public import ArtGallery.Orthogonal.BoundaryPoint.WingModel
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.CopyInc.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.CopyMatch.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.InvLe_1_200

/-! The chart and role records of profile `InvLe_1_200` for its nook copy tests (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.InvLe_1_200
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert CellCert CellRoles CopyChannel SpanCells RoomCoordinates ArtGallery.Orthogonal.Hard
open WingOrder.InvLe_1_200
set_option maxRecDepth 200000
set_option maxHeartbeats 0

abbrev C : Chart := SepWing.chartOf template cache boxes WingRecords.InvLe_1_200.index

theorem C_lit : C=SepData.InvLe_1_200.Chart.CL := SepData.InvLe_1_200.Chart.C_eq

/-- The emitted role records are the index data on the chart grid. -/
theorem records : CopySpec.Records template WingRecords.InvLe_1_200.index 2 := by
  unfold CopySpec.Records
  intro rs size n j hn hj hr s args
  obtain ⟨-,-,eq⟩ := WingModel.good_at_size (t:=template) (size ▸ WingBounds.InvLe_1_200.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,WingRecords.InvLe_1_200.records⟩
    (fun g hx hy => WingChart.InvLe_1_200.simple g hx hy) SepData.InvLe_1_200.cert (WingFill.InvLe_1_200.filled_eq size n j hn hj hr)
  exact CopyRecords.of_join eq

end ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.InvLe_1_200
end
