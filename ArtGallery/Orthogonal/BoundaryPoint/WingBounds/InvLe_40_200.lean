module

public import ArtGallery.Orthogonal.BoundaryPoint.WingEnvelopeCert
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.InvLe_40_200

/-! Uniform enclosure of this profile's actual staircase and arithmetic room. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingBounds.InvLe_40_200
open WingEnvelope WingEnvelopeCert ChartDrawing MarginCert

abbrev template : Template := ⟨BankCorridor.InvLe_40_200.layout,
  ⟨RoomFamily.InvLe.xAxis,RoomFamily.InvLe.yAxis,RoomFamily.InvLe.cells,RoomFamily.InvLe.roles⟩,WingChart.InvLe_40_200.chart⟩

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

theorem certificate : Cert template 2 where
  arithmetic := WingDoor.InvLe_40_200.checks
  x := by decide +kernel
  y := by decide +kernel
  rx := by decide +kernel
  ry := by decide +kernel

end ArtGallery.Orthogonal.BoundaryPoint.WingBounds.InvLe_40_200
end
