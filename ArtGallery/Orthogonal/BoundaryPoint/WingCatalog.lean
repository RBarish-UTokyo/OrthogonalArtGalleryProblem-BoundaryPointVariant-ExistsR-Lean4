module

public import ArtGallery.Orthogonal.BoundaryPoint.WingFinal.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingFinal.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingFinal.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingFinal.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingFinal.Lower_10_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingFinal.Lower_10_360_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingFinal.Lower_10_520_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingFinal.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.WingFinal.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingFinal.InvLe_1_360
public import ArtGallery.Orthogonal.BoundaryPoint.WingFinal.InvLe_1_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingFinal.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.WingFinal.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingFinal.InvRevGe_40_200

/-! # The wing catalogue

For every profile of the catalogue: its index data, the moving roles with their channels and
spots, the uniform wing cover `WingSpec.Cover`, the emitted records, and the shape of the role
records (`WingSpec.Entry`). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingCatalog
open ChartDrawing RoomGrid

/-- The moving roles of the profile of a tag. -/
def mvOf : Nat → List (Nat × Nat × Index × Index)
  | 0 => WingFinal.Ordinary_40_200_520.mv
  | 1 => WingFinal.Shifted_40_200_520.mv
  | 2 => WingFinal.Lower_40_200_1000.mv
  | 3 => WingFinal.Lower_10_40_1000.mv
  | 4 => WingFinal.Lower_10_200_1000.mv
  | 5 => WingFinal.Lower_10_360_1000.mv
  | 6 => WingFinal.Lower_10_520_1000.mv
  | 7 => WingFinal.InvLe_1_40.mv
  | 8 => WingFinal.InvLe_1_200.mv
  | 9 => WingFinal.InvLe_1_360.mv
  | 10 => WingFinal.InvLe_1_520.mv
  | 11 => WingFinal.InvRevGe_1_10.mv
  | 12 => WingFinal.InvLe_40_200.mv
  | 13 => WingFinal.InvRevGe_40_200.mv
  | _ => []

theorem cat : ∀ tag t, catalog[tag]?=some t → WingSpec.Entry t tag (mvOf tag) := by
  intro tag t ht
  have h14 : tag<14 := by
    by_contra h
    rw [List.getElem?_eq_none (by simp only [catalog,List.length_cons,List.length_nil]; omega)] at ht
    cases ht
  interval_cases tag
  · cases ht
    exact ⟨WingRecords.Ordinary_40_200_520.index,WingFinal.Ordinary_40_200_520.cover,CopyLocal.Ordinary_40_200_520.records,by decide +kernel,by decide +kernel⟩
  · cases ht
    exact ⟨WingRecords.Shifted_40_200_520.index,WingFinal.Shifted_40_200_520.cover,CopyLocal.Shifted_40_200_520.records,by decide +kernel,by decide +kernel⟩
  · cases ht
    exact ⟨WingRecords.Lower_40_200_1000.index,WingFinal.Lower_40_200_1000.cover,CopyLocal.Lower_40_200_1000.records,by decide +kernel,by decide +kernel⟩
  · cases ht
    exact ⟨WingRecords.Lower_10_40_1000.index,WingFinal.Lower_10_40_1000.cover,CopyLocal.Lower_10_40_1000.records,by decide +kernel,by decide +kernel⟩
  · cases ht
    exact ⟨WingRecords.Lower_10_200_1000.index,WingFinal.Lower_10_200_1000.cover,CopyLocal.Lower_10_200_1000.records,by decide +kernel,by decide +kernel⟩
  · cases ht
    exact ⟨WingRecords.Lower_10_360_1000.index,WingFinal.Lower_10_360_1000.cover,CopyLocal.Lower_10_360_1000.records,by decide +kernel,by decide +kernel⟩
  · cases ht
    exact ⟨WingRecords.Lower_10_520_1000.index,WingFinal.Lower_10_520_1000.cover,CopyLocal.Lower_10_520_1000.records,by decide +kernel,by decide +kernel⟩
  · cases ht
    exact ⟨WingRecords.InvLe_1_40.index,WingFinal.InvLe_1_40.cover,CopyLocal.InvLe_1_40.records,by decide +kernel,by decide +kernel⟩
  · cases ht
    exact ⟨WingRecords.InvLe_1_200.index,WingFinal.InvLe_1_200.cover,CopyLocal.InvLe_1_200.records,by decide +kernel,by decide +kernel⟩
  · cases ht
    exact ⟨WingRecords.InvLe_1_360.index,WingFinal.InvLe_1_360.cover,CopyLocal.InvLe_1_360.records,by decide +kernel,by decide +kernel⟩
  · cases ht
    exact ⟨WingRecords.InvLe_1_520.index,WingFinal.InvLe_1_520.cover,CopyLocal.InvLe_1_520.records,by decide +kernel,by decide +kernel⟩
  · cases ht
    exact ⟨WingRecords.InvRevGe_1_10.index,WingFinal.InvRevGe_1_10.cover,CopyLocal.InvRevGe_1_10.records,by decide +kernel,by decide +kernel⟩
  · cases ht
    exact ⟨WingRecords.InvLe_40_200.index,WingFinal.InvLe_40_200.cover,CopyLocal.InvLe_40_200.records,by decide +kernel,by decide +kernel⟩
  · cases ht
    exact ⟨WingRecords.InvRevGe_40_200.index,WingFinal.InvRevGe_40_200.cover,CopyLocal.InvRevGe_40_200.records,by decide +kernel,by decide +kernel⟩

end ArtGallery.Orthogonal.BoundaryPoint.WingCatalog
end
