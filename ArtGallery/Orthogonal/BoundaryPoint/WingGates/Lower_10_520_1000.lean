module

public import ArtGallery.Orthogonal.BoundaryPoint.WingEscape
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.Lower_10_520_1000

/-! A pocket witness invisible from the complete closed door for each full-wing role. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingGates.Lower_10_520_1000
open WingEscape WingOrder.Lower_10_520_1000 WingRecords.Lower_10_520_1000
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

-- g0_0
def w0 : CertPoint := (⟨(13,15,66,68),(13,66),false,false⟩,.back 0)
-- g1_0
def w1 : CertPoint := (⟨(46,47,77,79),(47,77),true,true⟩,.back 0)
-- g0_1
def w2 : CertPoint := (⟨(10,12,48,50),(10,48),false,false⟩,.back 0)
-- g1_1
def w3 : CertPoint := (⟨(33,34,59,61),(34,59),true,true⟩,.back 0)
-- g0_2
def w4 : CertPoint := (⟨(7,9,30,32),(7,30),false,false⟩,.back 0)
-- g1_2
def w5 : CertPoint := (⟨(20,21,41,43),(21,41),true,true⟩,.back 0)
-- gU0
def w6 : CertPoint := (⟨(40,42,21,22),(40,21),false,false⟩,.back 1)
-- gU1
def w7 : CertPoint := (⟨(27,29,21,22),(27,21),false,false⟩,.back 1)
-- gU_right
def w8 : CertPoint := (⟨(56,58,19,20),(56,19),false,false⟩,.side false 0 (0,0,2,0))
-- gR0
def w9 : CertPoint := (⟨(52,54,72,74),(54,72),true,true⟩,.side false 0 (0,0,2,0))
-- gR1
def w10 : CertPoint := (⟨(52,53,54,56),(53,54),true,true⟩,.side false 0 (0,1,3,0))
-- gR2
def w11 : CertPoint := (⟨(52,53,36,38),(53,36),true,true⟩,.side false 0 (0,1,3,0))
-- gFin
def w12 : CertPoint := (⟨(79,80,13,14),(79,14),true,false⟩,.back 0)
-- gFinSide
def w13 : CertPoint := (⟨(84,85,16,18),(84,16),true,false⟩,.back 0)
-- gFloor
def w14 : CertPoint := (⟨(73,74,0,1),(73,0),true,false⟩,.back 0)
-- q
def w15 : CertPoint := (⟨(59,61,6,7),(59,6),true,false⟩,.back 0)
-- r
def w16 : CertPoint := (⟨(90,91,8,9),(90,8),true,false⟩,.back 0)
-- x
def w17 : CertPoint := (⟨(65,66,4,5),(65,4),true,false⟩,.back 0)
-- z
def w18 : CertPoint := (⟨(69,70,2,3),(69,2),true,false⟩,.back 0)

def witnesses : List CertPoint := [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18]

theorem certificate : WingEscape.Cert template boxes cache index witnesses where
  valid := by decide +kernel
  aperture := by decide +kernel
  assignments := by decide +kernel

theorem hidden {ranks : List Nat} (size : ranks.length=3) (n j : Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈ranks,i≤n) :
    let s := (1:ℚ)/n
    WingEscape.Hidden template (s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)) :=
  WingEscape.at_size (size ▸ WingBounds.Lower_10_520_1000.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,records,certificate⟩ cell_indices (WingFill.Lower_10_520_1000.filled_eq size n j hn hj hr)

end ArtGallery.Orthogonal.BoundaryPoint.WingGates.Lower_10_520_1000
end
