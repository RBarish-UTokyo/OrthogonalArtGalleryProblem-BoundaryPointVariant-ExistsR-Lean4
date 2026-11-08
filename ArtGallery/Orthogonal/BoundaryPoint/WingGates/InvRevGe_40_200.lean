module

public import ArtGallery.Orthogonal.BoundaryPoint.WingEscape
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.InvRevGe_40_200

/-! A pocket witness invisible from the complete closed door for each full-wing role. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingGates.InvRevGe_40_200
open WingEscape WingOrder.InvRevGe_40_200 WingRecords.InvRevGe_40_200
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

-- g0_0
def w0 : CertPoint := (⟨(8,10,37,39),(8,37),false,false⟩,.back 0)
-- g1_0
def w1 : CertPoint := (⟨(28,29,46,48),(29,46),true,true⟩,.back 0)
-- g0_1
def w2 : CertPoint := (⟨(5,7,19,21),(5,19),false,false⟩,.back 0)
-- g1_1
def w3 : CertPoint := (⟨(15,16,30,32),(16,30),true,true⟩,.back 0)
-- gU0
def w4 : CertPoint := (⟨(22,24,13,14),(22,13),false,false⟩,.back 1)
-- gU_right
def w5 : CertPoint := (⟨(38,40,11,12),(38,11),false,false⟩,.side false 0 (0,1,3,1))
-- gR0
def w6 : CertPoint := (⟨(34,36,43,45),(36,43),true,true⟩,.side false 0 (0,1,3,0))
-- gR1
def w7 : CertPoint := (⟨(34,35,25,27),(35,25),true,true⟩,.side false 0 (0,1,3,0))
-- A
def w8 : CertPoint := (⟨(43,44,1,3),(43,1),true,false⟩,.back 0)
-- B
def w9 : CertPoint := (⟨(51,52,15,16),(51,16),false,true⟩,.side false 0 (0,0,2,0))
-- axis
def w10 : CertPoint := (⟨(55,56,0,1),(55,0),false,false⟩,.side false 0 (0,0,4,0))
-- low
def w11 : CertPoint := (⟨(57,59,0,1),(57,0),false,false⟩,.side false 0 (0,0,2,0))

def witnesses : List CertPoint := [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11]

theorem certificate : WingEscape.Cert template boxes cache index witnesses where
  valid := by decide +kernel
  aperture := by decide +kernel
  assignments := by decide +kernel

theorem hidden {ranks : List Nat} (size : ranks.length=2) (n j : Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈ranks,i≤n) :
    let s := (1:ℚ)/n
    WingEscape.Hidden template (s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)) :=
  WingEscape.at_size (size ▸ WingBounds.InvRevGe_40_200.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,records,certificate⟩ cell_indices (WingFill.InvRevGe_40_200.filled_eq size n j hn hj hr)

end ArtGallery.Orthogonal.BoundaryPoint.WingGates.InvRevGe_40_200
end
