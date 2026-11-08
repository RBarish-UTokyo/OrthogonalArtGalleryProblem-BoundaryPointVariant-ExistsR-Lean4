module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520.C1Defs

/-! Range data of profile `Ordinary_40_200_520`: `C1I3` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.Ordinary_40_200_520
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def c1hdrL : Ex := (.lit ([[[320]]] : P3))

noncomputable def c1hdrWqN : Ex := (.lit ([[],[[1]]] : P3))
noncomputable def c1hdrWqD : Ex := (.lit ([[[320]]] : P3))
noncomputable def c1hdrWqC : Ex := (.lit ([[[1]]] : P3))

theorem c1hdrWqcof : RegCert.auto (.sub (.mul c1hdrWqD c1hdrWqC) c1hdrL)=true := by decide +kernel

noncomputable def c1hdrX51N : Ex := c1N1218
noncomputable def c1hdrX51D : Ex := c1D1218
noncomputable def c1hdrX51C : Ex := (.lit ([[[1]]] : P3))

theorem c1hdrX51cof : RegCert.auto (.sub (.mul c1hdrX51D c1hdrX51C) c1hdrL)=true := by decide +kernel

noncomputable def c1hdroneN : Ex := (.lit ([[[1]]] : P3))
noncomputable def c1hdroneD : Ex := (.lit ([[[1]]] : P3))
noncomputable def c1hdroneC : Ex := (.lit ([[[320]]] : P3))

theorem c1hdronecof : RegCert.auto (.sub (.mul c1hdroneD c1hdroneC) c1hdrL)=true := by decide +kernel

theorem c1hdrok : RegCert.auto (linX (.mul c1hdroneN c1hdroneC) [(1,(.mul c1hdrX51N c1hdrX51C)),(-1,(.mul c1hdrWqN c1hdrWqC))])=true := by decide +kernel

noncomputable def c1hdrK : Ex := (.lit ([[[1]]] : P3))

theorem c1hdrLne : RegCert.auto (.sub (.mul c1hdrL c1hdrK) (.lit [[[320]]]))=true := by decide +kernel

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520
end
