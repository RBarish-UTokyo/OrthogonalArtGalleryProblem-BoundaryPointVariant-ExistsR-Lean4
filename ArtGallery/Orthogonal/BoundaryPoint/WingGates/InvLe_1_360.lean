module

public import ArtGallery.Orthogonal.BoundaryPoint.WingEscape
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.InvLe_1_360

/-! A pocket witness invisible from the complete closed door for each full-wing role. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingGates.InvLe_1_360
open WingEscape WingOrder.InvLe_1_360 WingRecords.InvLe_1_360
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

-- g0_0
def w0 : CertPoint := (⟨(8,10,38,40),(8,38),false,false⟩,.back 0)
-- g1_0
def w1 : CertPoint := (⟨(28,29,47,49),(29,47),true,true⟩,.back 0)
-- g0_1
def w2 : CertPoint := (⟨(5,7,20,22),(5,20),false,false⟩,.back 0)
-- g1_1
def w3 : CertPoint := (⟨(15,16,31,33),(16,31),true,true⟩,.back 0)
-- gU0
def w4 : CertPoint := (⟨(22,24,14,15),(22,14),false,false⟩,.back 1)
-- gU_right
def w5 : CertPoint := (⟨(38,40,12,13),(38,12),false,false⟩,.side false 0 (0,1,3,1))
-- gR0
def w6 : CertPoint := (⟨(34,36,44,46),(36,44),true,true⟩,.side false 0 (0,1,3,0))
-- gR1
def w7 : CertPoint := (⟨(34,35,26,28),(35,26),true,true⟩,.side false 0 (0,1,3,0))
-- A
def w8 : CertPoint := (⟨(43,44,1,3),(43,1),true,false⟩,.back 0)
-- B
def w9 : CertPoint := (⟨(55,56,16,17),(55,17),false,true⟩,.side false 0 (0,0,2,0))
-- axis
def w10 : CertPoint := (⟨(50,51,0,1),(50,0),false,false⟩,.side false 0 (0,0,4,0))
-- low
def w11 : CertPoint := (⟨(58,60,0,1),(58,0),false,false⟩,.side false 0 (0,0,2,0))

def witnesses : List CertPoint := [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11]

theorem certificate : WingEscape.Cert template boxes cache index witnesses where
  valid := by decide +kernel
  aperture := by decide +kernel
  assignments := by decide +kernel

theorem hidden {ranks : List Nat} (size : ranks.length=2) (n j : Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈ranks,i≤n) :
    let s := (1:ℚ)/n
    WingEscape.Hidden template (s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)) :=
  WingEscape.at_size (size ▸ WingBounds.InvLe_1_360.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,records,certificate⟩ cell_indices (WingFill.InvLe_1_360.filled_eq size n j hn hj hr)

end ArtGallery.Orthogonal.BoundaryPoint.WingGates.InvLe_1_360
end
