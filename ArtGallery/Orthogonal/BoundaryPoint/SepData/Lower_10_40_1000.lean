module

public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role0
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role1
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role2
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role3
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role4
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role5
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role6
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role7
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role8
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role9
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role10
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role11
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role12
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role13
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role14
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role15
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role16
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role17
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000.Role18
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Lower_10_40_1000

/-! Same-wing role separation for every admissible parameter of profile `Lower_10_40_1000` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000
open SepCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def anchors : List Nat := [Role0.anchor, Role1.anchor, Role2.anchor, Role3.anchor, Role4.anchor, Role5.anchor, Role6.anchor, Role7.anchor, Role8.anchor, Role9.anchor, Role10.anchor, Role11.anchor, Role12.anchor, Role13.anchor, Role14.anchor, Role15.anchor, Role16.anchor, Role17.anchor, Role18.anchor]

def certs : List (List Entry) := [Role0.entries, Role1.entries, Role2.entries, Role3.entries, Role4.entries, Role5.entries, Role6.entries, Role7.entries, Role8.entries, Role9.entries, Role10.entries, Role11.entries, Role12.entries, Role13.entries, Role14.entries, Role15.entries, Role16.entries, Role17.entries, Role18.entries]

theorem roles_length : WingRecords.Lower_10_40_1000.index.2.length=19 := by decide +kernel

theorem cert : SepWing.Cert WingOrder.Lower_10_40_1000.template WingOrder.Lower_10_40_1000.cache WingOrder.Lower_10_40_1000.boxes
    WingRecords.Lower_10_40_1000.index anchors certs where
  axis := WingChart.Lower_10_40_1000.axis_edges
  verts := WingChart.Lower_10_40_1000.indices
  tiles := WingRecords.Lower_10_40_1000.cell_indices
  cells := by decide +kernel
  bottom := ⟨44,by decide +kernel⟩
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

theorem profile : RoleSeparation.Profile anchors WingOrder.Lower_10_40_1000.template 3 := by
  intro rs size n j hn hj hr
  exact SepWing.at_size (t:=WingOrder.Lower_10_40_1000.template) (size ▸ WingBounds.Lower_10_40_1000.certificate) n j hn hj hr
    ⟨WingOrder.Lower_10_40_1000.sizes,WingOrder.Lower_10_40_1000.verified,WingOrder.Lower_10_40_1000.x_ok,WingOrder.Lower_10_40_1000.y_ok,
      WingRecords.Lower_10_40_1000.records⟩
    (fun g hx hy => WingChart.Lower_10_40_1000.simple g hx hy) cert (WingFill.Lower_10_40_1000.filled_eq size n j hn hj hr)

end ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000
end
