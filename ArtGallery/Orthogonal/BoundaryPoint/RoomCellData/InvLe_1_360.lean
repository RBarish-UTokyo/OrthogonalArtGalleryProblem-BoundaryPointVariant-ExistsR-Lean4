module

public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_1_360.Chart
public import ArtGallery.Orthogonal.BoundaryPoint.RoomCell
public import ArtGallery.Orthogonal.BoundaryPoint.CellRoles
public import ArtGallery.Orthogonal.BoundaryPoint.WingModel
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_1_360

/-! Chain certificates of the critical room cells of the `InvLe_1_360` wing chart (generated): each
from the spot of one room role, with assumed window ends that follow from its primary corners. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomCellData.InvLe_1_360
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert SepWing CoverChain CoverAssume CellRoles
open WingOrder.InvLe_1_360
set_option maxRecDepth 200000
set_option maxHeartbeats 0

abbrev C : SepCert.Chart := chartOf template cache boxes WingRecords.InvLe_1_360.index

theorem C_lit : C=SepData.InvLe_1_360.Chart.CL := SepData.InvLe_1_360.Chart.C_eq

/-- Cell `(48, 49, 7, 8)` from the spot of role 8. -/
def cert0 : CertA := ⟨[33,39,34],[⟨⟨true,true,47,4,16⟩,[.zzero,.zlit 1 (0,0,0,0) 45 1 48 7 47 16,.zzero,.zlit 1 (0,0,0,0) 45 1 49 7 47 16,.zzero,.zlit 1 (0,0,0,0) 45 1 48 8 47 16,.zzero,.zlit 1 (0,0,0,0) 45 1 49 8 47 16,.zzero,.zlit 1 (0,0,0,0) 46 1 48 7 47 16,.zzero,.zlit 1 (0,0,0,0) 46 1 49 7 47 16,.zzero,.zlit 1 (0,0,0,0) 46 1 48 8 47 16,.zzero,.zlit 1 (0,0,0,0) 46 1 49 8 47 16],1,0⟩,⟨⟨true,true,48,4,16⟩,[.zzero,.zlit 1 (0,0,0,0) 45 1 48 7 48 16,.zzero,.zlit 1 (0,0,0,0) 45 1 49 7 48 16,.zzero,.zlit 1 (0,0,0,0) 45 1 48 8 48 16,.zzero,.zlit 1 (0,0,0,0) 45 1 49 8 48 16,.zzero,.zlit 1 (0,0,0,0) 46 1 48 7 48 16,.zzero,.zlit 1 (0,0,0,0) 46 1 49 7 48 16,.zzero,.zlit 1 (0,0,0,0) 46 1 48 8 48 16,.zzero,.zlit 1 (0,0,0,0) 46 1 49 8 48 16],1,0⟩]⟩
theorem cert0_ok : cert0.ok C (45, 1) (46, 1) 48 49 7 8=true := by (try rw [C_lit]); decide +kernel
theorem cert0_prim : RoomCell.primOK C [((47,4),false)] (45, 1) (46, 1) 48 49 7 8 cert0=true := by (try rw [C_lit]); decide +kernel

/-- Cell `(49, 50, 7, 8)` from the spot of role 8. -/
def cert1 : CertA := ⟨[33,39,34,36],[⟨⟨true,true,47,4,16⟩,[.zzero,.zlit 1 (0,0,0,0) 45 1 49 7 47 16,.zzero,.zlit 1 (0,0,0,0) 45 1 50 7 47 16,.zzero,.zlit 1 (0,0,0,0) 45 1 49 8 47 16,.zzero,.zlit 1 (0,0,0,0) 45 1 50 8 47 16,.zzero,.zlit 1 (0,0,0,0) 46 1 49 7 47 16,.zzero,.zlit 1 (0,0,0,0) 46 1 50 7 47 16,.zzero,.zlit 1 (0,0,0,0) 46 1 49 8 47 16,.zzero,.zlit 1 (0,0,0,0) 46 1 50 8 47 16],1,0⟩,⟨⟨true,true,48,4,16⟩,[.zzero,.zlit 1 (0,0,0,0) 45 1 49 7 48 16,.zzero,.zlit 1 (0,0,0,0) 45 1 50 7 48 16,.zzero,.zlit 1 (0,0,0,0) 45 1 49 8 48 16,.zzero,.zlit 1 (0,0,0,0) 45 1 50 8 48 16,.zzero,.zlit 1 (0,0,0,0) 46 1 49 7 48 16,.zzero,.zlit 1 (0,0,0,0) 46 1 50 7 48 16,.zzero,.zlit 1 (0,0,0,0) 46 1 49 8 48 16,.zzero,.zlit 1 (0,0,0,0) 46 1 50 8 48 16],1,0⟩,⟨⟨true,true,49,1,8⟩,[.zzero,.zlit 1 (0,0,0,0) 45 1 49 7 49 8,.zzero,.zlit 1 (0,0,0,0) 45 1 50 7 49 8,.zzero,.zzero,.zzero,.zlit 2 (2,0,2,0) 50 8 49 8 45 1,.zzero,.zlit 1 (0,0,0,0) 46 1 49 7 49 8,.zzero,.zlit 1 (0,0,0,0) 46 1 50 7 49 8,.zzero,.zzero,.zzero,.zlit 2 (2,0,2,0) 50 8 49 8 46 1],2,0⟩]⟩
theorem cert1_ok : cert1.ok C (45, 1) (46, 1) 49 50 7 8=true := by (try rw [C_lit]); decide +kernel
theorem cert1_prim : RoomCell.primOK C [((47,4),false)] (45, 1) (46, 1) 49 50 7 8 cert1=true := by (try rw [C_lit]); decide +kernel

/-- Cell `(48, 49, 7, 8)` from the spot of role 9. -/
def cert2 : CertA := ⟨[37,38,35,36,34],[⟨⟨true,false,54,1,7⟩,[.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero],2,1⟩,⟨⟨true,false,52,1,7⟩,[.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero],2,1⟩,⟨⟨true,false,50,1,8⟩,[.zzero,.zlit 1 (0,0,0,0) 48 7 55 1 50 8,.zzero,.zlit 1 (2,0,0,2) 49 7 55 1 50 8,.zzero,.zlit 1 (0,0,0,0) 48 8 55 1 50 8,.zzero,.zlit 1 (0,2,0,2) 49 8 55 1 50 8,.zzero,.zlit 1 (0,0,0,0) 48 7 56 1 50 8,.zzero,.zlit 1 (2,0,0,2) 49 7 56 1 50 8,.zzero,.zlit 1 (0,0,0,0) 48 8 56 1 50 8,.zzero,.zlit 1 (0,2,0,2) 49 8 56 1 50 8],2,0⟩,⟨⟨true,false,49,1,8⟩,[.zzero,.zlit 1 (0,0,0,0) 48 7 55 1 49 8,.zzero,.zlit 1 (2,0,0,2) 49 7 55 1 49 8,.zzero,.zlit 1 (0,0,0,0) 48 8 55 1 49 8,.zzero,.zzero,.zzero,.zlit 1 (0,0,0,0) 48 7 56 1 49 8,.zzero,.zlit 1 (2,0,0,2) 49 7 56 1 49 8,.zzero,.zlit 1 (0,0,0,0) 48 8 56 1 49 8,.zzero,.zzero],2,0⟩]⟩
theorem cert2_ok : cert2.ok C (55, 1) (56, 1) 48 49 7 8=true := by (try rw [C_lit]); decide +kernel
theorem cert2_prim : RoomCell.primOK C [((52,7),false)] (55, 1) (56, 1) 48 49 7 8 cert2=true := by (try rw [C_lit]); decide +kernel

/-- Cell `(49, 50, 7, 8)` from the spot of role 9. -/
def cert3 : CertA := ⟨[37,38,35,36],[⟨⟨true,false,54,1,7⟩,[.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero],2,1⟩,⟨⟨true,false,52,1,7⟩,[.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero],2,1⟩,⟨⟨true,false,50,1,8⟩,[.zzero,.zlit 1 (2,0,0,2) 49 7 55 1 50 8,.zzero,.zlit 1 (2,0,0,2) 50 7 55 1 50 8,.zzero,.zlit 1 (0,2,0,2) 49 8 55 1 50 8,.zzero,.zzero,.zzero,.zlit 1 (2,0,0,2) 49 7 56 1 50 8,.zzero,.zlit 1 (2,0,0,2) 50 7 56 1 50 8,.zzero,.zlit 1 (0,2,0,2) 49 8 56 1 50 8,.zzero,.zzero],2,0⟩]⟩
theorem cert3_ok : cert3.ok C (55, 1) (56, 1) 49 50 7 8=true := by (try rw [C_lit]); decide +kernel
theorem cert3_prim : RoomCell.primOK C [((52,7),false)] (55, 1) (56, 1) 49 50 7 8 cert3=true := by (try rw [C_lit]); decide +kernel

end ArtGallery.Orthogonal.BoundaryPoint.RoomCellData.InvLe_1_360
end
