module

public import ArtGallery.Orthogonal.BoundaryPoint.WingPrivacy
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.Lower_10_200_1000

/-! Every individual private tip is invisible from the closed door in this full wing. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.Lower_10_200_1000
open WingPrivacy WingOrder.Lower_10_200_1000 WingRecords.Lower_10_200_1000
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

-- g0_0
def role0 : List Route := [.pocket ⟨(13,15,66,68),(13,66),false,false⟩ (.back 0),
  .pocket ⟨(13,15,66,68),(15,66),false,false⟩ (.back 0),
  .pocket ⟨(4,6,69,70),(4,70),true,false⟩ (.side false 0 (0,0,3,0))]

-- g1_0
def role1 : List Route := [.pocket ⟨(46,47,77,79),(47,77),true,true⟩ (.back 0),
  .pocket ⟨(46,47,77,79),(47,79),true,true⟩ (.back 0),
  .pocket ⟨(44,45,80,81),(44,81),false,true⟩ (.side true 0 (0,0,3,0))]

-- g0_1
def role2 : List Route := [.pocket ⟨(10,12,48,50),(10,48),false,false⟩ (.back 0),
  .pocket ⟨(10,12,48,50),(12,48),false,false⟩ (.back 0),
  .pocket ⟨(2,5,51,52),(2,52),true,false⟩ (.side false 0 (0,0,3,0))]

-- g1_1
def role3 : List Route := [.pocket ⟨(33,34,59,61),(34,59),true,true⟩ (.back 0),
  .pocket ⟨(33,34,59,61),(34,61),true,true⟩ (.back 0),
  .pocket ⟨(31,32,62,63),(31,63),false,true⟩ (.side true 0 (0,0,3,0))]

-- g0_2
def role4 : List Route := [.pocket ⟨(7,9,30,32),(7,30),false,false⟩ (.back 0),
  .pocket ⟨(7,9,30,32),(9,30),false,false⟩ (.back 0),
  .pocket ⟨(0,3,33,34),(0,34),true,false⟩ (.side false 0 (0,0,3,0))]

-- g1_2
def role5 : List Route := [.pocket ⟨(20,21,41,43),(21,41),true,true⟩ (.back 0),
  .pocket ⟨(20,21,41,43),(21,43),true,true⟩ (.back 0),
  .pocket ⟨(18,19,44,45),(18,45),false,true⟩ (.side true 0 (0,0,3,0))]

-- gU0
def role6 : List Route := [.pocket ⟨(40,42,21,22),(40,21),false,false⟩ (.back 1),
  .pocket ⟨(40,42,21,22),(42,21),false,false⟩ (.back 1),
  .pocket ⟨(37,38,64,65),(37,65),true,false⟩ (.side false 0 (0,0,2,0))]

-- gU1
def role7 : List Route := [.pocket ⟨(27,29,21,22),(27,21),false,false⟩ (.back 1),
  .pocket ⟨(27,29,21,22),(29,21),false,false⟩ (.back 1),
  .pocket ⟨(24,25,46,47),(24,47),true,false⟩ (.side false 0 (0,0,2,0))]

-- gU_right
def role8 : List Route := [.pocket ⟨(56,58,19,20),(56,19),false,false⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(56,58,19,20),(58,19),false,false⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(60,62,28,29),(62,29),true,true⟩ (.side false 0 (0,0,2,0))]

-- gR0
def role9 : List Route := [.pocket ⟨(52,54,72,74),(54,72),true,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(52,54,72,74),(54,74),true,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(48,49,75,76),(48,76),false,true⟩ (.side true 0 (0,0,2,0))]

-- gR1
def role10 : List Route := [.pocket ⟨(52,53,54,56),(53,54),true,true⟩ (.side false 0 (0,1,3,0)),
  .pocket ⟨(52,53,54,56),(53,56),true,true⟩ (.side false 0 (0,1,3,0)),
  .pocket ⟨(35,36,57,58),(35,58),false,true⟩ (.side true 0 (0,1,3,0))]

-- gR2
def role11 : List Route := [.pocket ⟨(52,53,36,38),(53,36),true,true⟩ (.side false 0 (0,1,3,0)),
  .pocket ⟨(52,53,36,38),(53,38),true,true⟩ (.side false 0 (0,1,3,0)),
  .pocket ⟨(22,23,39,40),(22,40),false,true⟩ (.side true 0 (0,1,3,0))]

-- gFin
def role12 : List Route := [.pocket ⟨(81,83,11,12),(81,11),false,false⟩ (.side false 0 (0,0,0,0)),
  .pocket ⟨(81,83,11,12),(83,11),false,false⟩ (.side false 0 (0,0,0,0)),
  .pocket ⟨(79,80,13,14),(79,14),true,false⟩ (.back 0)]

-- gFinSide
def role13 : List Route := [.pocket ⟨(84,85,16,18),(84,16),true,false⟩ (.back 0),
  .pocket ⟨(84,85,16,18),(84,18),true,false⟩ (.back 0),
  .pocket ⟨(86,87,25,27),(87,27),false,true⟩ (.side false 0 (0,0,0,0))]

-- gFloor
def role14 : List Route := [.pocket ⟨(75,77,25,27),(75,27),false,true⟩ (.side false 0 (0,0,0,0)),
  .pocket ⟨(75,77,25,27),(77,27),false,true⟩ (.side false 0 (0,0,0,0)),
  .pocket ⟨(73,74,0,1),(73,0),true,false⟩ (.back 0)]

-- q
def role15 : List Route := [.pocket ⟨(63,64,25,27),(63,27),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(63,64,25,27),(64,27),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(59,61,6,7),(59,6),true,false⟩ (.back 0)]

-- r
def role16 : List Route := [.pocket ⟨(94,95,25,27),(94,27),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(94,95,25,27),(95,27),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(90,91,8,9),(90,8),true,false⟩ (.back 0)]

-- x
def role17 : List Route := [.pocket ⟨(67,68,25,27),(67,27),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(67,68,25,27),(68,27),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(65,66,4,5),(65,4),true,false⟩ (.back 0)]

-- z
def role18 : List Route := [.pocket ⟨(71,72,25,27),(71,27),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(71,72,25,27),(72,27),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(69,70,2,3),(69,2),true,false⟩ (.back 0)]

def routes : List Route := role0++role1++role2++role3++role4++role5++role6++role7++role8++role9++role10++role11++role12++role13++role14++role15++role16++role17++role18

theorem certificate : WingPrivacy.Cert template boxes cache index routes where
  geometry := by decide +kernel
  numeric := by decide +kernel
  registered := by decide +kernel

theorem all_hidden {ranks : List Nat} (size : ranks.length=3) (n j : Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈ranks,i≤n) :
    let s := (1:ℚ)/n
    WingPrivacy.AllHidden template (s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)) :=
  WingPrivacy.at_size (size ▸ WingBounds.Lower_10_200_1000.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,records,certificate⟩ cell_indices (WingFill.Lower_10_200_1000.filled_eq size n j hn hj hr)

end ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.Lower_10_200_1000
end
