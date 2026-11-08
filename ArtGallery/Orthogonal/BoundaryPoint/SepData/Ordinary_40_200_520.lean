module

public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role0
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role1
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role2
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role3
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role4
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role5
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role6
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role7
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role8
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role9
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role10
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role11
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role12
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role13
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role14
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role15
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role16
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role17
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Role18
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Ordinary_40_200_520

/-! Same-wing role separation for every admissible parameter of profile `Ordinary_40_200_520` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520
open SepCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def anchors : List Nat := [Role0.anchor, Role1.anchor, Role2.anchor, Role3.anchor, Role4.anchor, Role5.anchor, Role6.anchor, Role7.anchor, Role8.anchor, Role9.anchor, Role10.anchor, Role11.anchor, Role12.anchor, Role13.anchor, Role14.anchor, Role15.anchor, Role16.anchor, Role17.anchor, Role18.anchor]

def certs : List (List Entry) := [Role0.entries, Role1.entries, Role2.entries, Role3.entries, Role4.entries, Role5.entries, Role6.entries, Role7.entries, Role8.entries, Role9.entries, Role10.entries, Role11.entries, Role12.entries, Role13.entries, Role14.entries, Role15.entries, Role16.entries, Role17.entries, Role18.entries]

theorem roles_length : WingRecords.Ordinary_40_200_520.index.2.length=19 := by decide +kernel

theorem cert : SepWing.Cert WingOrder.Ordinary_40_200_520.template WingOrder.Ordinary_40_200_520.cache WingOrder.Ordinary_40_200_520.boxes
    WingRecords.Ordinary_40_200_520.index anchors certs where
  axis := WingChart.Ordinary_40_200_520.axis_edges
  verts := WingChart.Ordinary_40_200_520.indices
  tiles := WingRecords.Ordinary_40_200_520.cell_indices
  cells := by decide +kernel
  bottom := ⟨34,by decide +kernel⟩
  six := by decide +kernel
  inRange := by decide +kernel
  roles := by
    intro i hi
    rw [roles_length] at hi
    interval_cases i
    · exact Role0.ok
    · exact Role1.ok
    · exact Role2.ok
    · exact Role3.ok
    · exact Role4.ok
    · exact Role5.ok
    · exact Role6.ok
    · exact Role7.ok
    · exact Role8.ok
    · exact Role9.ok
    · exact Role10.ok
    · exact Role11.ok
    · exact Role12.ok
    · exact Role13.ok
    · exact Role14.ok
    · exact Role15.ok
    · exact Role16.ok
    · exact Role17.ok
    · exact Role18.ok

theorem profile : RoleSeparation.Profile anchors WingOrder.Ordinary_40_200_520.template 3 := by
  intro rs size n j hn hj hr
  exact SepWing.at_size (t:=WingOrder.Ordinary_40_200_520.template) (size ▸ WingBounds.Ordinary_40_200_520.certificate) n j hn hj hr
    ⟨WingOrder.Ordinary_40_200_520.sizes,WingOrder.Ordinary_40_200_520.verified,WingOrder.Ordinary_40_200_520.x_ok,WingOrder.Ordinary_40_200_520.y_ok,
      WingRecords.Ordinary_40_200_520.records⟩
    (fun g hx hy => WingChart.Ordinary_40_200_520.simple g hx hy) cert (WingFill.Ordinary_40_200_520.filled_eq size n j hn hj hr)

end ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520
end
