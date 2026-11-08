module

public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvRevGe_1_10.Chart
public import ArtGallery.Orthogonal.BoundaryPoint.CopySpec
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRecords
public import ArtGallery.Orthogonal.BoundaryPoint.WingModel
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.CopyInc.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.CopyMatch.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.InvRevGe_1_10

/-! The chart and role records of profile `InvRevGe_1_10` for its nook copy tests (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.InvRevGe_1_10
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert CellCert CellRoles CopyChannel SpanCells RoomCoordinates ArtGallery.Orthogonal.Hard
open WingOrder.InvRevGe_1_10
set_option maxRecDepth 200000
set_option maxHeartbeats 0

abbrev C : Chart := SepWing.chartOf template cache boxes WingRecords.InvRevGe_1_10.index

theorem C_lit : C=SepData.InvRevGe_1_10.Chart.CL := SepData.InvRevGe_1_10.Chart.C_eq

/-- The emitted role records are the index data on the chart grid. -/
theorem records : CopySpec.Records template WingRecords.InvRevGe_1_10.index 2 := by
  unfold CopySpec.Records
  intro rs size n j hn hj hr s args
  obtain ⟨-,-,eq⟩ := WingModel.good_at_size (t:=template) (size ▸ WingBounds.InvRevGe_1_10.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,WingRecords.InvRevGe_1_10.records⟩
    (fun g hx hy => WingChart.InvRevGe_1_10.simple g hx hy) SepData.InvRevGe_1_10.cert (WingFill.InvRevGe_1_10.filled_eq size n j hn hj hr)
  exact CopyRecords.of_join eq

end ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.InvRevGe_1_10
end
