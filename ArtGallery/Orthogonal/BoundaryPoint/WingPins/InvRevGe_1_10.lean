module

public import ArtGallery.Orthogonal.BoundaryPoint.WingPinProof
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.InvRevGe_1_10

/-! Every allowed guard interval in this complete wing is forced by its three private witnesses. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingPins.InvRevGe_1_10
open PinGridData WingOrder.InvRevGe_1_10 WingRecords.InvRevGe_1_10
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

theorem edges_zip : GridSweep.allEdges template.chart.cycle.points=
    template.chart.cycle.points.zip (template.chart.cycle.points.tail++template.chart.cycle.points.take 1) := by
  decide +kernel

-- g0_0
def pin0 : Pin × RegisterProduct.Hint := (⟨⟨false, false, true⟩, 8, 10, 41, 39, 37, 2, 4, 40, 39, (8,10,37,39), (2,4,40,41)⟩,(1,0,0,3))
theorem contact0 : PinContact.check pin0.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- g1_0
def pin1 : Pin × RegisterProduct.Hint := (⟨⟨true, true, false⟩, 48, 46, 26, 28, 29, 50, 49, 27, 28, (28,29,46,48), (26,27,49,50)⟩,(1,0,0,3))
theorem contact1 : PinContact.check pin1.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- g0_1
def pin2 : Pin × RegisterProduct.Hint := (⟨⟨false, false, true⟩, 5, 7, 23, 21, 19, 1, 3, 22, 21, (5,7,19,21), (1,3,22,23)⟩,(1,0,0,3))
theorem contact2 : PinContact.check pin2.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- g1_1
def pin3 : Pin × RegisterProduct.Hint := (⟨⟨true, true, false⟩, 32, 30, 13, 15, 16, 34, 33, 14, 15, (15,16,30,32), (13,14,33,34)⟩,(1,0,0,3))
theorem contact3 : PinContact.check pin3.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gU0
def pin4 : Pin × RegisterProduct.Hint := (⟨⟨false, false, true⟩, 22, 24, 36, 14, 13, 19, 21, 35, 14, (22,24,13,14), (19,21,35,36)⟩,(0,1,1,2))
theorem contact4 : PinContact.check pin4.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gU_right
def pin5 : Pin × RegisterProduct.Hint := (⟨⟨false, true, true⟩, 40, 38, 18, 12, 11, 42, 41, 17, 12, (38,40,11,12), (41,42,17,18)⟩,(0,1,0,2))
theorem contact5 : PinContact.check pin5.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gR0
def pin6 : Pin × RegisterProduct.Hint := (⟨⟨true, true, false⟩, 45, 43, 30, 34, 36, 52, 51, 31, 34, (34,36,43,45), (30,31,51,52)⟩,(0,1,0,2))
theorem contact6 : PinContact.check pin6.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gR1
def pin7 : Pin × RegisterProduct.Hint := (⟨⟨true, true, false⟩, 27, 25, 17, 34, 35, 29, 28, 18, 34, (34,35,25,27), (17,18,28,29)⟩,(0,1,1,3))
theorem contact7 : PinContact.check pin7.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- A
def pin8 : Pin × RegisterProduct.Hint := (⟨⟨false, false, false⟩, 45, 46, 1, 15, 16, 43, 44, 3, 15, (45,46,15,16), (43,44,1,3)⟩,(0,2,0,2))
theorem contact8 : PinContact.check pin8.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- B
def pin9 : Pin × RegisterProduct.Hint := (⟨⟨false, true, false⟩, 52, 51, 1, 15, 16, 54, 53, 2, 15, (51,52,15,16), (53,54,1,2)⟩,(0,4,2,4))
theorem contact9 : PinContact.check pin9.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- axis
def pin10 : Pin × RegisterProduct.Hint := (⟨⟨true, false, false⟩, 5, 7, 55, 61, 62, 0, 1, 56, 61, (61,62,5,7), (55,56,0,1)⟩,(2,0,0,4))
theorem contact10 : PinContact.check pin10.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- low
def pin11 : Pin × RegisterProduct.Hint := (⟨⟨false, true, true⟩, 59, 57, 10, 1, 0, 63, 61, 9, 1, (57,59,0,1), (61,63,9,10)⟩,(0,2,2,2))
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
  WingPinProof.at_size (size ▸ WingBounds.InvRevGe_1_10.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,records,certificate⟩ WingChart.InvRevGe_1_10.axis_edges WingChart.InvRevGe_1_10.indices cell_indices
    (WingFill.InvRevGe_1_10.filled_eq size n j hn hj hr)

end ArtGallery.Orthogonal.BoundaryPoint.WingPins.InvRevGe_1_10
end
