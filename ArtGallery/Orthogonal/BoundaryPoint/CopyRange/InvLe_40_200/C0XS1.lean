module

public import ArtGallery.Orthogonal.BoundaryPoint.RowLit.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_40_200.C0XDefs

/-! Range data of profile `InvLe_40_200`: `C0XS1` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_40_200
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.InvLe_40_200
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem c0k99 : (c0s99).out (1/65:ℚ) (199/5005:ℚ) (797/18590:ℚ) rows boxes c0ins [c0f109]=some c0f99 := by (try rw [RowLit.InvLe_40_200.out_eq]); (try rw [RowLit.InvLe_40_200.check_eq]); decide +kernel

theorem c0k95 : (c0s95).out (1/65:ℚ) (199/5005:ℚ) (797/18590:ℚ) rows boxes c0ins [c0f106,c0f99]=some c0f95 := by (try rw [RowLit.InvLe_40_200.out_eq]); (try rw [RowLit.InvLe_40_200.check_eq]); decide +kernel

theorem c0k94 : (c0s94).out (1/65:ℚ) (199/5005:ℚ) (797/18590:ℚ) rows boxes c0ins [c0f341,c0f95]=some c0f94 := by (try rw [RowLit.InvLe_40_200.out_eq]); (try rw [RowLit.InvLe_40_200.check_eq]); decide +kernel

theorem c0k93 : (c0s93).out (1/65:ℚ) (199/5005:ℚ) (797/18590:ℚ) rows boxes c0ins [c0f109,c0f94]=some c0f93 := by (try rw [RowLit.InvLe_40_200.out_eq]); (try rw [RowLit.InvLe_40_200.check_eq]); decide +kernel

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_40_200
end
