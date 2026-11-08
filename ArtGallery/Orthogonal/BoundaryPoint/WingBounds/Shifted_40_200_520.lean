module

public import ArtGallery.Orthogonal.BoundaryPoint.WingEnvelopeCert
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.Shifted_40_200_520

/-! Uniform enclosure of this profile's actual staircase and arithmetic room. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Shifted_40_200_520
open WingEnvelope WingEnvelopeCert ChartDrawing MarginCert

abbrev template : Template := ⟨BankCorridor.Shifted_40_200_520.layout,
  ⟨RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,RoomFamily.Shifted.cells,RoomFamily.Shifted.roles⟩,WingChart.Shifted_40_200_520.chart⟩

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

theorem certificate : Cert template 3 where
  arithmetic := WingDoor.Shifted_40_200_520.checks
  x := by decide +kernel
  y := by decide +kernel
  rx := by decide +kernel
  ry := by decide +kernel

end ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Shifted_40_200_520
end
