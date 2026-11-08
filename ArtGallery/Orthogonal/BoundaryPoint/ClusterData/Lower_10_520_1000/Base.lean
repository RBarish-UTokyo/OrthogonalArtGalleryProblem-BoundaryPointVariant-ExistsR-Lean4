module

public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_520_1000.Chart
public import ArtGallery.Orthogonal.BoundaryPoint.NookCell
public import ArtGallery.Orthogonal.BoundaryPoint.CellRoles
public import ArtGallery.Orthogonal.BoundaryPoint.WingModel
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_520_1000

/-! The chart of the copy-cluster cells of `Lower_10_520_1000` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.ClusterData.Lower_10_520_1000
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert SepWing CoverChain CoverAssume CellRoles
open WingOrder.Lower_10_520_1000
set_option maxRecDepth 200000
set_option maxHeartbeats 0

abbrev C : SepCert.Chart := chartOf template cache boxes WingRecords.Lower_10_520_1000.index

theorem C_lit : C=SepData.Lower_10_520_1000.Chart.CL := SepData.Lower_10_520_1000.Chart.C_eq

end ArtGallery.Orthogonal.BoundaryPoint.ClusterData.Lower_10_520_1000
end
