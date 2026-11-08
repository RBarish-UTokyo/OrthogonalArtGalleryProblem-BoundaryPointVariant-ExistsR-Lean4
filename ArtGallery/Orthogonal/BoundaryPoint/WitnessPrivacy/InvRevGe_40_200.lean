module

public import ArtGallery.Orthogonal.BoundaryPoint.WingPrivacy
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.InvRevGe_40_200

/-! Every individual private tip is invisible from the closed door in this full wing. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.InvRevGe_40_200
open WingPrivacy WingOrder.InvRevGe_40_200 WingRecords.InvRevGe_40_200
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

-- g0_0
def role0 : List Route := [.pocket ⟨(8,10,37,39),(8,37),false,false⟩ (.back 0),
  .pocket ⟨(8,10,37,39),(10,37),false,false⟩ (.back 0),
  .pocket ⟨(3,4,40,41),(3,41),true,false⟩ (.side false 0 (0,0,3,0))]

-- g1_0
def role1 : List Route := [.pocket ⟨(28,29,46,48),(29,46),true,true⟩ (.back 0),
  .pocket ⟨(28,29,46,48),(29,48),true,true⟩ (.back 0),
  .pocket ⟨(26,27,49,50),(26,50),false,true⟩ (.side true 0 (0,0,3,0))]

-- g0_1
def role2 : List Route := [.pocket ⟨(5,7,19,21),(5,19),false,false⟩ (.back 0),
  .pocket ⟨(5,7,19,21),(7,19),false,false⟩ (.back 0),
  .pocket ⟨(0,2,22,23),(0,23),true,false⟩ (.side false 0 (0,0,3,0))]

-- g1_1
def role3 : List Route := [.pocket ⟨(15,16,30,32),(16,30),true,true⟩ (.back 0),
  .pocket ⟨(15,16,30,32),(16,32),true,true⟩ (.back 0),
  .pocket ⟨(13,14,33,34),(13,34),false,true⟩ (.side true 0 (0,0,3,0))]

-- gU0
def role4 : List Route := [.pocket ⟨(22,24,13,14),(22,13),false,false⟩ (.back 1),
  .pocket ⟨(22,24,13,14),(24,13),false,false⟩ (.back 1),
  .pocket ⟨(19,21,35,36),(19,36),true,false⟩ (.side false 0 (0,1,2,0))]

-- gU_right
def role5 : List Route := [.pocket ⟨(38,40,11,12),(38,11),false,false⟩ (.side false 0 (0,1,3,1)),
  .pocket ⟨(38,40,11,12),(40,11),false,false⟩ (.side false 0 (0,1,3,1)),
  .pocket ⟨(41,42,17,18),(42,18),true,true⟩ (.side false 0 (0,1,2,0))]

-- gR0
def role6 : List Route := [.pocket ⟨(34,36,43,45),(36,43),true,true⟩ (.side false 0 (0,1,3,0)),
  .pocket ⟨(34,36,43,45),(36,45),true,true⟩ (.side false 0 (0,1,3,0)),
  .pocket ⟨(30,31,51,52),(30,52),false,true⟩ (.side true 0 (0,1,2,0))]

-- gR1
def role7 : List Route := [.pocket ⟨(34,35,25,27),(35,25),true,true⟩ (.side false 0 (0,1,3,0)),
  .pocket ⟨(34,35,25,27),(35,27),true,true⟩ (.side false 0 (0,1,3,0)),
  .pocket ⟨(17,18,28,29),(17,29),false,true⟩ (.side true 0 (0,1,3,0))]

-- A
def role8 : List Route := [.pocket ⟨(45,46,15,16),(45,16),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(45,46,15,16),(46,16),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(43,44,1,3),(43,1),true,false⟩ (.back 0)]

-- B
def role9 : List Route := [.pocket ⟨(51,52,15,16),(51,16),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(51,52,15,16),(52,16),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(53,54,1,2),(54,1),true,true⟩ (.side true 0 (0,4,4,0))]

-- axis
def role10 : List Route := [.slice ⟨(62,5),11,38,1,(0,0,0,1)⟩,
  .slice ⟨(62,7),11,38,1,(0,0,0,1)⟩,
  .pocket ⟨(55,56,0,1),(55,0),false,false⟩ (.side false 0 (0,0,4,0))]

-- low
def role11 : List Route := [.pocket ⟨(57,59,0,1),(57,0),false,false⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(57,59,0,1),(59,0),false,false⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(61,63,9,10),(63,10),true,true⟩ (.side true 0 (0,2,2,0))]

def routes : List Route := role0++role1++role2++role3++role4++role5++role6++role7++role8++role9++role10++role11

theorem certificate : WingPrivacy.Cert template boxes cache index routes where
  geometry := by decide +kernel
  numeric := by decide +kernel
  registered := by decide +kernel

theorem all_hidden {ranks : List Nat} (size : ranks.length=2) (n j : Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈ranks,i≤n) :
    let s := (1:ℚ)/n
    WingPrivacy.AllHidden template (s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)) :=
  WingPrivacy.at_size (size ▸ WingBounds.InvRevGe_40_200.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,records,certificate⟩ cell_indices (WingFill.InvRevGe_40_200.filled_eq size n j hn hj hr)

end ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.InvRevGe_40_200
end
