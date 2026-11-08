module

public import ArtGallery.Orthogonal.BoundaryPoint.DoorFenceCert
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Shifted_40_200_520

/-! A separating half-plane or the door channel on every emitted edge. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingFence.Shifted_40_200_520
open DoorFenceCert
def hints : List Side := [.north, .north, .north, .north, .north, .north, .north, .north, .north, .channel, .channel, .channel, .north, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north]
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem checked : check WingBounds.Shifted_40_200_520.template hints=true := by decide +kernel

end ArtGallery.Orthogonal.BoundaryPoint.WingFence.Shifted_40_200_520
end
