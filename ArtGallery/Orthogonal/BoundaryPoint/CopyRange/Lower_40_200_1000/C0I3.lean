module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000.C0Defs

/-! Range data of profile `Lower_40_200_1000`: `C0I3` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.Lower_40_200_1000
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def c0hdrL : Ex := (.lit ([[[320]]] : P3))

noncomputable def c0hdrWqN : Ex := (.lit ([[],[[1]]] : P3))
noncomputable def c0hdrWqD : Ex := (.lit ([[[320]]] : P3))
noncomputable def c0hdrWqC : Ex := (.lit ([[[1]]] : P3))

theorem c0hdrWqcof : RegCert.auto (.sub (.mul c0hdrWqD c0hdrWqC) c0hdrL)=true := by decide +kernel

noncomputable def c0hdrX51N : Ex := c0N1216
noncomputable def c0hdrX51D : Ex := c0D1216
noncomputable def c0hdrX51C : Ex := (.lit ([[[1]]] : P3))

theorem c0hdrX51cof : RegCert.auto (.sub (.mul c0hdrX51D c0hdrX51C) c0hdrL)=true := by decide +kernel

noncomputable def c0hdroneN : Ex := (.lit ([[[1]]] : P3))
noncomputable def c0hdroneD : Ex := (.lit ([[[1]]] : P3))
noncomputable def c0hdroneC : Ex := (.lit ([[[320]]] : P3))

theorem c0hdronecof : RegCert.auto (.sub (.mul c0hdroneD c0hdroneC) c0hdrL)=true := by decide +kernel

theorem c0hdrok : RegCert.auto (linX (.mul c0hdroneN c0hdroneC) [(1,(.mul c0hdrX51N c0hdrX51C)),(-1,(.mul c0hdrWqN c0hdrWqC))])=true := by decide +kernel

noncomputable def c0hdrK : Ex := (.lit ([[[1]]] : P3))

theorem c0hdrLne : RegCert.auto (.sub (.mul c0hdrL c0hdrK) (.lit [[[320]]]))=true := by decide +kernel

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000
end
