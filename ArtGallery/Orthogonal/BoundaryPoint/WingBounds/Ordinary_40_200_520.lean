module

public import ArtGallery.Orthogonal.BoundaryPoint.WingEnvelopeCert
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.Ordinary_40_200_520

/-! Uniform enclosure of this profile's actual staircase and arithmetic room. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Ordinary_40_200_520
open WingEnvelope WingEnvelopeCert ChartDrawing MarginCert

abbrev template : Template := ⟨BankCorridor.Ordinary_40_200_520.layout,
  ⟨RoomFamily.Ordinary.xAxis,RoomFamily.Ordinary.yAxis,RoomFamily.Ordinary.cells,RoomFamily.Ordinary.roles⟩,WingChart.Ordinary_40_200_520.chart⟩

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

theorem certificate : Cert template 3 where
  arithmetic := WingDoor.Ordinary_40_200_520.checks
  x := by decide +kernel
  y := by decide +kernel
  rx := by decide +kernel
  ry := by decide +kernel

end ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Ordinary_40_200_520
end
