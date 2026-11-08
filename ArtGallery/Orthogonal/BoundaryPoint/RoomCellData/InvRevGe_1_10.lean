module

public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvRevGe_1_10.Chart
public import ArtGallery.Orthogonal.BoundaryPoint.RoomCell
public import ArtGallery.Orthogonal.BoundaryPoint.CellRoles
public import ArtGallery.Orthogonal.BoundaryPoint.WingModel
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvRevGe_1_10

/-! Chain certificates of the critical room cells of the `InvRevGe_1_10` wing chart (generated): each
from the spot of one room role, with assumed window ends that follow from its primary corners. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomCellData.InvRevGe_1_10
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert SepWing CoverChain CoverAssume CellRoles
open WingOrder.InvRevGe_1_10
set_option maxRecDepth 200000
set_option maxHeartbeats 0

abbrev C : SepCert.Chart := chartOf template cache boxes WingRecords.InvRevGe_1_10.index

theorem C_lit : C=SepData.InvRevGe_1_10.Chart.CL := SepData.InvRevGe_1_10.Chart.C_eq

/-- Cell `(53, 54, 10, 11)` from the spot of role 8. -/
def cert0 : CertA := ⟨[33,37,39,38,34,36],[⟨⟨true,true,47,1,6⟩,[.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero],2,1⟩,⟨⟨true,true,48,4,6⟩,[.zlit 1 (0,0,0,0) 53 10 45 1 48 4,.zzero,.zlit 1 (0,0,0,0) 54 10 45 1 48 4,.zzero,.zlit 1 (0,0,0,0) 53 11 45 1 48 4,.zzero,.zlit 1 (0,0,0,0) 54 11 45 1 48 4,.zzero,.zlit 1 (0,0,0,0) 53 10 46 1 48 4,.zzero,.zlit 1 (0,0,0,0) 54 10 46 1 48 4,.zzero,.zlit 1 (0,0,0,0) 53 11 46 1 48 4,.zzero,.zlit 1 (0,0,0,0) 54 11 46 1 48 4,.zzero],0,1⟩,⟨⟨true,true,49,4,6⟩,[.zlit 1 (0,0,0,0) 53 10 45 1 49 4,.zzero,.zlit 1 (0,0,0,0) 54 10 45 1 49 4,.zzero,.zlit 1 (0,0,0,0) 53 11 45 1 49 4,.zzero,.zlit 1 (0,0,0,0) 54 11 45 1 49 4,.zzero,.zlit 1 (0,0,0,0) 53 10 46 1 49 4,.zzero,.zlit 1 (0,0,0,0) 54 10 46 1 49 4,.zzero,.zlit 1 (0,0,0,0) 53 11 46 1 49 4,.zzero,.zlit 1 (0,0,0,0) 54 11 46 1 49 4,.zzero],0,1⟩,⟨⟨true,true,50,1,6⟩,[.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero],2,1⟩,⟨⟨true,true,53,8,15⟩,[.zlit 1 (0,2,0,2) 53 10 45 1 53 8,.zlit 1 (0,0,0,0) 45 1 53 10 53 15,.zlit 1 (0,2,0,2) 54 10 45 1 53 8,.zlit 1 (0,0,0,0) 45 1 54 10 53 15,.zlit 1 (0,0,0,0) 53 11 45 1 53 8,.zlit 2 (1,0,1,0) 53 11 53 15 45 1,.zlit 1 (0,0,0,0) 54 11 45 1 53 8,.zlit 2 (1,0,1,0) 54 11 53 15 45 1,.zlit 1 (0,2,0,2) 53 10 46 1 53 8,.zlit 1 (0,0,0,0) 46 1 53 10 53 15,.zlit 1 (0,2,0,2) 54 10 46 1 53 8,.zlit 1 (0,0,0,0) 46 1 54 10 53 15,.zlit 1 (0,0,0,0) 53 11 46 1 53 8,.zlit 2 (1,0,1,0) 53 11 53 15 46 1,.zlit 1 (0,0,0,0) 54 11 46 1 53 8,.zlit 2 (1,0,1,0) 54 11 53 15 46 1],0,0⟩]⟩
theorem cert0_ok : cert0.ok C (45, 1) (46, 1) 53 54 10 11=true := by (try rw [C_lit]); decide +kernel
theorem cert0_prim : RoomCell.primOK C [((50,6),true)] (45, 1) (46, 1) 53 54 10 11 cert0=true := by (try rw [C_lit]); decide +kernel

/-- Cell `(54, 55, 10, 11)` from the spot of role 8. -/
def cert1 : CertA := ⟨[33,37,39,38,34,36],[⟨⟨true,true,47,1,6⟩,[.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero],2,1⟩,⟨⟨true,true,48,4,6⟩,[.zlit 1 (0,0,0,0) 54 10 45 1 48 4,.zzero,.zlit 1 (0,0,0,0) 55 10 45 1 48 4,.zzero,.zlit 1 (0,0,0,0) 54 11 45 1 48 4,.zzero,.zlit 1 (0,0,0,0) 55 11 45 1 48 4,.zzero,.zlit 1 (0,0,0,0) 54 10 46 1 48 4,.zzero,.zlit 1 (0,0,0,0) 55 10 46 1 48 4,.zzero,.zlit 1 (0,0,0,0) 54 11 46 1 48 4,.zzero,.zlit 1 (0,0,0,0) 55 11 46 1 48 4,.zzero],0,1⟩,⟨⟨true,true,49,4,6⟩,[.zlit 1 (0,0,0,0) 54 10 45 1 49 4,.zzero,.zlit 1 (0,0,0,0) 55 10 45 1 49 4,.zzero,.zlit 1 (0,0,0,0) 54 11 45 1 49 4,.zzero,.zlit 1 (0,0,0,0) 55 11 45 1 49 4,.zzero,.zlit 1 (0,0,0,0) 54 10 46 1 49 4,.zzero,.zlit 1 (0,0,0,0) 55 10 46 1 49 4,.zzero,.zlit 1 (0,0,0,0) 54 11 46 1 49 4,.zzero,.zlit 1 (0,0,0,0) 55 11 46 1 49 4,.zzero],0,1⟩,⟨⟨true,true,50,1,6⟩,[.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero,.zzero],2,1⟩,⟨⟨true,true,53,8,15⟩,[.zlit 1 (0,2,0,2) 54 10 45 1 53 8,.zlit 1 (0,0,0,0) 45 1 54 10 53 15,.zlit 1 (0,2,0,2) 55 10 45 1 53 8,.zlit 1 (0,0,0,0) 45 1 55 10 53 15,.zlit 1 (0,0,0,0) 54 11 45 1 53 8,.zlit 2 (1,0,1,0) 54 11 53 15 45 1,.zlit 1 (0,0,0,0) 55 11 45 1 53 8,.zlit 2 (1,0,1,0) 55 11 53 15 45 1,.zlit 1 (0,2,0,2) 54 10 46 1 53 8,.zlit 1 (0,0,0,0) 46 1 54 10 53 15,.zlit 1 (0,2,0,2) 55 10 46 1 53 8,.zlit 1 (0,0,0,0) 46 1 55 10 53 15,.zlit 1 (0,0,0,0) 54 11 46 1 53 8,.zlit 2 (1,0,1,0) 54 11 53 15 46 1,.zlit 1 (0,0,0,0) 55 11 46 1 53 8,.zlit 2 (1,0,1,0) 55 11 53 15 46 1],0,0⟩]⟩
theorem cert1_ok : cert1.ok C (45, 1) (46, 1) 54 55 10 11=true := by (try rw [C_lit]); decide +kernel
theorem cert1_prim : RoomCell.primOK C [((50,6),true)] (45, 1) (46, 1) 54 55 10 11 cert1=true := by (try rw [C_lit]); decide +kernel

/-- Cell `(53, 54, 10, 11)` from the spot of role 9. -/
def cert2 : CertA := ⟨[34,36],[⟨⟨true,true,53,8,15⟩,[.zzero,.zlit 1 (2,0,0,2) 51 1 53 10 53 15,.zzero,.zlit 1 (2,0,0,2) 51 1 54 10 53 15,.zzero,.zlit 2 (3,0,1,2) 53 11 53 15 51 1,.zzero,.zlit 2 (3,0,1,2) 54 11 53 15 51 1,.zzero,.zlit 1 (2,0,0,2) 52 1 53 10 53 15,.zzero,.zlit 1 (2,0,0,2) 52 1 54 10 53 15,.zzero,.zlit 2 (3,0,1,2) 53 11 53 15 52 1,.zzero,.zlit 2 (3,0,1,2) 54 11 53 15 52 1],1,0⟩]⟩
theorem cert2_ok : cert2.ok C (51, 1) (52, 1) 53 54 10 11=true := by (try rw [C_lit]); decide +kernel
theorem cert2_prim : RoomCell.primOK C [((53,8),false)] (51, 1) (52, 1) 53 54 10 11 cert2=true := by (try rw [C_lit]); decide +kernel

/-- Cell `(54, 55, 10, 11)` from the spot of role 9. -/
def cert3 : CertA := ⟨[34,36],[⟨⟨true,true,53,8,15⟩,[.zzero,.zlit 1 (2,0,0,2) 51 1 54 10 53 15,.zzero,.zlit 1 (2,0,0,2) 51 1 55 10 53 15,.zzero,.zlit 2 (3,0,1,2) 54 11 53 15 51 1,.zzero,.zlit 2 (3,0,1,2) 55 11 53 15 51 1,.zzero,.zlit 1 (2,0,0,2) 52 1 54 10 53 15,.zzero,.zlit 1 (2,0,0,2) 52 1 55 10 53 15,.zzero,.zlit 2 (3,0,1,2) 54 11 53 15 52 1,.zzero,.zlit 2 (3,0,1,2) 55 11 53 15 52 1],1,0⟩]⟩
theorem cert3_ok : cert3.ok C (51, 1) (52, 1) 54 55 10 11=true := by (try rw [C_lit]); decide +kernel
theorem cert3_prim : RoomCell.primOK C [((53,8),false)] (51, 1) (52, 1) 54 55 10 11 cert3=true := by (try rw [C_lit]); decide +kernel

end ArtGallery.Orthogonal.BoundaryPoint.RoomCellData.InvRevGe_1_10
end
