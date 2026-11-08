module

public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_40_200.Role0
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_40_200.Role1
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_40_200.Role2
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_40_200.Role3
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_40_200.Role4
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_40_200.Role5
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_40_200.Role6
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_40_200.Role7
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_40_200.Role8
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_40_200.Role9
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_40_200.Role10
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_40_200.Role11
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.InvLe_40_200

/-! Same-wing role separation for every admissible parameter of profile `InvLe_40_200` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_40_200
open SepCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def anchors : List Nat := [Role0.anchor, Role1.anchor, Role2.anchor, Role3.anchor, Role4.anchor, Role5.anchor, Role6.anchor, Role7.anchor, Role8.anchor, Role9.anchor, Role10.anchor, Role11.anchor]

def certs : List (List Entry) := [Role0.entries, Role1.entries, Role2.entries, Role3.entries, Role4.entries, Role5.entries, Role6.entries, Role7.entries, Role8.entries, Role9.entries, Role10.entries, Role11.entries]

theorem roles_length : WingRecords.InvLe_40_200.index.2.length=12 := by decide +kernel

theorem cert : SepWing.Cert WingOrder.InvLe_40_200.template WingOrder.InvLe_40_200.cache WingOrder.InvLe_40_200.boxes
    WingRecords.InvLe_40_200.index anchors certs where
  axis := WingChart.InvLe_40_200.axis_edges
  verts := WingChart.InvLe_40_200.indices
  tiles := WingRecords.InvLe_40_200.cell_indices
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

theorem profile : RoleSeparation.Profile anchors WingOrder.InvLe_40_200.template 2 := by
  intro rs size n j hn hj hr
  exact SepWing.at_size (t:=WingOrder.InvLe_40_200.template) (size ▸ WingBounds.InvLe_40_200.certificate) n j hn hj hr
    ⟨WingOrder.InvLe_40_200.sizes,WingOrder.InvLe_40_200.verified,WingOrder.InvLe_40_200.x_ok,WingOrder.InvLe_40_200.y_ok,
      WingRecords.InvLe_40_200.records⟩
    (fun g hx hy => WingChart.InvLe_40_200.simple g hx hy) cert (WingFill.InvLe_40_200.filled_eq size n j hn hj hr)

end ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_40_200
end
