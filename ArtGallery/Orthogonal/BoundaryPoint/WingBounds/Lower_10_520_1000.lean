module

public import ArtGallery.Orthogonal.BoundaryPoint.WingEnvelopeCert
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.Lower_10_520_1000

/-! Uniform enclosure of this profile's actual staircase and arithmetic room. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Lower_10_520_1000
open WingEnvelope WingEnvelopeCert ChartDrawing MarginCert

abbrev template : Template := ⟨BankCorridor.Lower_10_520_1000.layout,
  ⟨RoomFamily.Lower.xAxis,RoomFamily.Lower.yAxis,RoomFamily.Lower.cells,RoomFamily.Lower.roles⟩,WingChart.Lower_10_520_1000.chart⟩

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

theorem certificate : Cert template 3 where
  arithmetic := WingDoor.Lower_10_520_1000.checks
  x := by decide +kernel
  y := by decide +kernel
  rx := by decide +kernel
  ry := by decide +kernel

end ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Lower_10_520_1000
end
