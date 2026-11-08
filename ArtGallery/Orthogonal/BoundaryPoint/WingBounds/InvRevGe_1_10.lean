module

public import ArtGallery.Orthogonal.BoundaryPoint.WingEnvelopeCert
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.InvRevGe_1_10

/-! Uniform enclosure of this profile's actual staircase and arithmetic room. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingBounds.InvRevGe_1_10
open WingEnvelope WingEnvelopeCert ChartDrawing MarginCert

abbrev template : Template := ⟨BankCorridor.InvRevGe_1_10.layout,
  ⟨RoomFamily.InvRevGe.xAxis,RoomFamily.InvRevGe.yAxis,RoomFamily.InvRevGe.cells,RoomFamily.InvRevGe.roles⟩,WingChart.InvRevGe_1_10.chart⟩

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

theorem certificate : Cert template 2 where
  arithmetic := WingDoor.InvRevGe_1_10.checks
  x := by decide +kernel
  y := by decide +kernel
  rx := by decide +kernel
  ry := by decide +kernel

end ArtGallery.Orthogonal.BoundaryPoint.WingBounds.InvRevGe_1_10
end
