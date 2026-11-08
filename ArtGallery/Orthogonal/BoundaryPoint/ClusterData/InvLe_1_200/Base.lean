module

public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_1_200.Chart
public import ArtGallery.Orthogonal.BoundaryPoint.NookCell
public import ArtGallery.Orthogonal.BoundaryPoint.CellRoles
public import ArtGallery.Orthogonal.BoundaryPoint.WingModel
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_1_200

/-! The chart of the copy-cluster cells of `InvLe_1_200` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.ClusterData.InvLe_1_200
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert SepWing CoverChain CoverAssume CellRoles
open WingOrder.InvLe_1_200
set_option maxRecDepth 200000
set_option maxHeartbeats 0

abbrev C : SepCert.Chart := chartOf template cache boxes WingRecords.InvLe_1_200.index

theorem C_lit : C=SepData.InvLe_1_200.Chart.CL := SepData.InvLe_1_200.Chart.C_eq

end ArtGallery.Orthogonal.BoundaryPoint.ClusterData.InvLe_1_200
end
