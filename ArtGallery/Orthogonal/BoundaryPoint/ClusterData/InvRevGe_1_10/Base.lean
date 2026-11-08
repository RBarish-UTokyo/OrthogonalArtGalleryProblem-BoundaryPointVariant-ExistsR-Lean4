module

public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvRevGe_1_10.Chart
public import ArtGallery.Orthogonal.BoundaryPoint.NookCell
public import ArtGallery.Orthogonal.BoundaryPoint.CellRoles
public import ArtGallery.Orthogonal.BoundaryPoint.WingModel
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvRevGe_1_10

/-! The chart of the copy-cluster cells of `InvRevGe_1_10` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.ClusterData.InvRevGe_1_10
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert SepWing CoverChain CoverAssume CellRoles
open WingOrder.InvRevGe_1_10
set_option maxRecDepth 200000
set_option maxHeartbeats 0

abbrev C : SepCert.Chart := chartOf template cache boxes WingRecords.InvRevGe_1_10.index

theorem C_lit : C=SepData.InvRevGe_1_10.Chart.CL := SepData.InvRevGe_1_10.Chart.C_eq

end ArtGallery.Orthogonal.BoundaryPoint.ClusterData.InvRevGe_1_10
end
