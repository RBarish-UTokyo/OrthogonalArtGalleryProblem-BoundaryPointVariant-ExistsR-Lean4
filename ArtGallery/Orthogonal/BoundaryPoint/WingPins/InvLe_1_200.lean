module

public import ArtGallery.Orthogonal.BoundaryPoint.WingPinProof
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.InvLe_1_200

/-! Every allowed guard interval in this complete wing is forced by its three private witnesses. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingPins.InvLe_1_200
open PinGridData WingOrder.InvLe_1_200 WingRecords.InvLe_1_200
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

theorem edges_zip : GridSweep.allEdges template.chart.cycle.points=
    template.chart.cycle.points.zip (template.chart.cycle.points.tail++template.chart.cycle.points.take 1) := by
  decide +kernel

-- g0_0
def pin0 : Pin × RegisterProduct.Hint := (⟨⟨false, false, true⟩, 8, 10, 42, 40, 38, 3, 4, 41, 40, (8,10,38,40), (3,4,41,42)⟩,(1,0,0,3))
theorem contact0 : PinContact.check pin0.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- g1_0
def pin1 : Pin × RegisterProduct.Hint := (⟨⟨true, true, false⟩, 49, 47, 26, 28, 29, 51, 50, 27, 28, (28,29,47,49), (26,27,50,51)⟩,(1,0,0,3))
theorem contact1 : PinContact.check pin1.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- g0_1
def pin2 : Pin × RegisterProduct.Hint := (⟨⟨false, false, true⟩, 5, 7, 24, 22, 20, 0, 2, 23, 22, (5,7,20,22), (0,2,23,24)⟩,(1,0,0,3))
theorem contact2 : PinContact.check pin2.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- g1_1
def pin3 : Pin × RegisterProduct.Hint := (⟨⟨true, true, false⟩, 33, 31, 13, 15, 16, 35, 34, 14, 15, (15,16,31,33), (13,14,34,35)⟩,(1,0,0,3))
theorem contact3 : PinContact.check pin3.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gU0
def pin4 : Pin × RegisterProduct.Hint := (⟨⟨false, false, true⟩, 22, 24, 37, 15, 14, 19, 21, 36, 15, (22,24,14,15), (19,21,36,37)⟩,(0,1,1,2))
theorem contact4 : PinContact.check pin4.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gU_right
def pin5 : Pin × RegisterProduct.Hint := (⟨⟨false, true, true⟩, 40, 38, 19, 13, 12, 42, 41, 18, 13, (38,40,12,13), (41,42,18,19)⟩,(0,1,0,2))
theorem contact5 : PinContact.check pin5.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gR0
def pin6 : Pin × RegisterProduct.Hint := (⟨⟨true, true, false⟩, 46, 44, 30, 34, 36, 53, 52, 31, 34, (34,36,44,46), (30,31,52,53)⟩,(0,1,0,2))
theorem contact6 : PinContact.check pin6.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gR1
def pin7 : Pin × RegisterProduct.Hint := (⟨⟨true, true, false⟩, 28, 26, 17, 34, 35, 30, 29, 18, 34, (34,35,26,28), (17,18,29,30)⟩,(0,1,1,3))
theorem contact7 : PinContact.check pin7.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- A
def pin8 : Pin × RegisterProduct.Hint := (⟨⟨false, false, false⟩, 45, 46, 1, 16, 17, 43, 44, 3, 16, (45,46,16,17), (43,44,1,3)⟩,(0,2,0,2))
theorem contact8 : PinContact.check pin8.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- B
def pin9 : Pin × RegisterProduct.Hint := (⟨⟨false, true, false⟩, 56, 55, 1, 16, 17, 62, 61, 2, 16, (55,56,16,17), (61,62,1,2)⟩,(0,2,2,4))
theorem contact9 : PinContact.check pin9.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- axis
def pin10 : Pin × RegisterProduct.Hint := (⟨⟨true, false, false⟩, 9, 11, 50, 52, 53, 0, 1, 51, 52, (52,53,9,11), (50,51,0,1)⟩,(4,0,0,4))
theorem contact10 : PinContact.check pin10.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- low
def pin11 : Pin × RegisterProduct.Hint := (⟨⟨false, true, true⟩, 60, 58, 6, 1, 0, 62, 61, 5, 1, (58,60,0,1), (61,62,5,6)⟩,(0,2,2,2))
theorem contact11 : PinContact.check pin11.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

def pins : List (Pin × RegisterProduct.Hint) := [pin0, pin1, pin2, pin3, pin4, pin5, pin6, pin7, pin8, pin9, pin10, pin11]

theorem certificate : WingPinProof.Cert template cache boxes index pins where
  valid := by decide +kernel
  nodes := by decide +kernel
  contacts := (Bool.and_eq_true_iff.mpr ⟨contact0,(Bool.and_eq_true_iff.mpr ⟨contact1,(Bool.and_eq_true_iff.mpr ⟨contact2,(Bool.and_eq_true_iff.mpr ⟨contact3,(Bool.and_eq_true_iff.mpr ⟨contact4,(Bool.and_eq_true_iff.mpr ⟨contact5,(Bool.and_eq_true_iff.mpr ⟨contact6,(Bool.and_eq_true_iff.mpr ⟨contact7,(Bool.and_eq_true_iff.mpr ⟨contact8,(Bool.and_eq_true_iff.mpr ⟨contact9,(Bool.and_eq_true_iff.mpr ⟨contact10,(Bool.and_eq_true_iff.mpr ⟨contact11,rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  gaps := by decide +kernel
  assignments := by decide +kernel

theorem localized {ranks : List Nat} (size : ranks.length=2) (n j : Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈ranks,i≤n) :
    let s := (1:ℚ)/n
    WingPinProof.Forces template (s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)) :=
  WingPinProof.at_size (size ▸ WingBounds.InvLe_1_200.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,records,certificate⟩ WingChart.InvLe_1_200.axis_edges WingChart.InvLe_1_200.indices cell_indices
    (WingFill.InvLe_1_200.filled_eq size n j hn hj hr)

end ArtGallery.Orthogonal.BoundaryPoint.WingPins.InvLe_1_200
end
