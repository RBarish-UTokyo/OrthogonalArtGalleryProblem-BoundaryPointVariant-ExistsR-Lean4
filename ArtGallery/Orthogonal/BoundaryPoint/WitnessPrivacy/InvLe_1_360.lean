module

public import ArtGallery.Orthogonal.BoundaryPoint.WingPrivacy
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.InvLe_1_360

/-! Every individual private tip is invisible from the closed door in this full wing. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.InvLe_1_360
open WingPrivacy WingOrder.InvLe_1_360 WingRecords.InvLe_1_360
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

-- g0_0
def role0 : List Route := [.pocket ⟨(8,10,38,40),(8,38),false,false⟩ (.back 0),
  .pocket ⟨(8,10,38,40),(10,38),false,false⟩ (.back 0),
  .pocket ⟨(3,4,41,42),(3,42),true,false⟩ (.side false 0 (0,0,3,0))]

-- g1_0
def role1 : List Route := [.pocket ⟨(28,29,47,49),(29,47),true,true⟩ (.back 0),
  .pocket ⟨(28,29,47,49),(29,49),true,true⟩ (.back 0),
  .pocket ⟨(26,27,50,51),(26,51),false,true⟩ (.side true 0 (0,0,3,0))]

-- g0_1
def role2 : List Route := [.pocket ⟨(5,7,20,22),(5,20),false,false⟩ (.back 0),
  .pocket ⟨(5,7,20,22),(7,20),false,false⟩ (.back 0),
  .pocket ⟨(0,1,23,24),(0,24),true,false⟩ (.side false 0 (0,0,3,0))]

-- g1_1
def role3 : List Route := [.pocket ⟨(15,16,31,33),(16,31),true,true⟩ (.back 0),
  .pocket ⟨(15,16,31,33),(16,33),true,true⟩ (.back 0),
  .pocket ⟨(13,14,34,35),(13,35),false,true⟩ (.side true 0 (0,0,3,0))]

-- gU0
def role4 : List Route := [.pocket ⟨(22,24,14,15),(22,14),false,false⟩ (.back 1),
  .pocket ⟨(22,24,14,15),(24,14),false,false⟩ (.back 1),
  .pocket ⟨(19,21,36,37),(19,37),true,false⟩ (.side false 0 (0,1,2,0))]

-- gU_right
def role5 : List Route := [.pocket ⟨(38,40,12,13),(38,12),false,false⟩ (.side false 0 (0,1,3,1)),
  .pocket ⟨(38,40,12,13),(40,12),false,false⟩ (.side false 0 (0,1,3,1)),
  .pocket ⟨(41,42,18,19),(42,19),true,true⟩ (.side false 0 (0,1,2,0))]

-- gR0
def role6 : List Route := [.pocket ⟨(34,36,44,46),(36,44),true,true⟩ (.side false 0 (0,1,3,0)),
  .pocket ⟨(34,36,44,46),(36,46),true,true⟩ (.side false 0 (0,1,3,0)),
  .pocket ⟨(30,31,52,53),(30,53),false,true⟩ (.side true 0 (0,1,2,0))]

-- gR1
def role7 : List Route := [.pocket ⟨(34,35,26,28),(35,26),true,true⟩ (.side false 0 (0,1,3,0)),
  .pocket ⟨(34,35,26,28),(35,28),true,true⟩ (.side false 0 (0,1,3,0)),
  .pocket ⟨(17,18,29,30),(17,30),false,true⟩ (.side true 0 (0,1,3,0))]

-- A
def role8 : List Route := [.pocket ⟨(45,46,16,17),(45,17),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(45,46,16,17),(46,17),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(43,44,1,3),(43,1),true,false⟩ (.back 0)]

-- B
def role9 : List Route := [.pocket ⟨(55,56,16,17),(55,17),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(55,56,16,17),(56,17),false,true⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(61,62,1,2),(62,1),true,true⟩ (.side true 0 (0,2,4,0))]

-- axis
def role10 : List Route := [.slice ⟨(53,9),12,38,1,(0,0,0,1)⟩,
  .slice ⟨(53,11),12,38,1,(0,0,0,1)⟩,
  .pocket ⟨(50,51,0,1),(50,0),false,false⟩ (.side false 0 (0,0,4,0))]

-- low
def role11 : List Route := [.pocket ⟨(58,60,0,1),(58,0),false,false⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(58,60,0,1),(60,0),false,false⟩ (.side false 0 (0,0,2,0)),
  .pocket ⟨(61,62,5,6),(62,6),true,true⟩ (.side true 0 (0,2,2,0))]

def routes : List Route := role0++role1++role2++role3++role4++role5++role6++role7++role8++role9++role10++role11

theorem certificate : WingPrivacy.Cert template boxes cache index routes where
  geometry := by decide +kernel
  numeric := by decide +kernel
  registered := by decide +kernel

theorem all_hidden {ranks : List Nat} (size : ranks.length=2) (n j : Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈ranks,i≤n) :
    let s := (1:ℚ)/n
    WingPrivacy.AllHidden template (s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)) :=
  WingPrivacy.at_size (size ▸ WingBounds.InvLe_1_360.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,records,certificate⟩ cell_indices (WingFill.InvLe_1_360.filled_eq size n j hn hj hr)

end ArtGallery.Orthogonal.BoundaryPoint.WitnessPrivacy.InvLe_1_360
end
