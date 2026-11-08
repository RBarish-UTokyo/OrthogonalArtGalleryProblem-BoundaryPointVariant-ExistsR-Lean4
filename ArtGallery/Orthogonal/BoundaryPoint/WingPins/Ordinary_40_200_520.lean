module

public import ArtGallery.Orthogonal.BoundaryPoint.WingPinProof
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.Ordinary_40_200_520

/-! Every allowed guard interval in this complete wing is forced by its three private witnesses. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingPins.Ordinary_40_200_520
open PinGridData WingOrder.Ordinary_40_200_520 WingRecords.Ordinary_40_200_520
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

theorem edges_zip : GridSweep.allEdges template.chart.cycle.points=
    template.chart.cycle.points.zip (template.chart.cycle.points.tail++template.chart.cycle.points.take 1) := by
  decide +kernel

-- g0_0
def pin0 : Pin × RegisterProduct.Hint := (⟨⟨false, false, true⟩, 13, 15, 70, 68, 66, 3, 6, 69, 68, (13,15,66,68), (3,6,69,70)⟩,(1,0,0,3))
theorem contact0 : PinContact.check pin0.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- g1_0
def pin1 : Pin × RegisterProduct.Hint := (⟨⟨true, true, false⟩, 79, 77, 44, 46, 47, 81, 80, 45, 46, (46,47,77,79), (44,45,80,81)⟩,(1,0,0,3))
theorem contact1 : PinContact.check pin1.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- g0_1
def pin2 : Pin × RegisterProduct.Hint := (⟨⟨false, false, true⟩, 10, 12, 52, 50, 48, 2, 5, 51, 50, (10,12,48,50), (2,5,51,52)⟩,(1,0,0,3))
theorem contact2 : PinContact.check pin2.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- g1_1
def pin3 : Pin × RegisterProduct.Hint := (⟨⟨true, true, false⟩, 61, 59, 31, 33, 34, 63, 62, 32, 33, (33,34,59,61), (31,32,62,63)⟩,(1,0,0,3))
theorem contact3 : PinContact.check pin3.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- g0_2
def pin4 : Pin × RegisterProduct.Hint := (⟨⟨false, false, true⟩, 7, 9, 34, 32, 30, 1, 4, 33, 32, (7,9,30,32), (1,4,33,34)⟩,(1,0,0,3))
theorem contact4 : PinContact.check pin4.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- g1_2
def pin5 : Pin × RegisterProduct.Hint := (⟨⟨true, true, false⟩, 43, 41, 18, 20, 21, 45, 44, 19, 20, (20,21,41,43), (18,19,44,45)⟩,(1,0,0,3))
theorem contact5 : PinContact.check pin5.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gU0
def pin6 : Pin × RegisterProduct.Hint := (⟨⟨false, false, true⟩, 40, 42, 65, 22, 21, 37, 39, 64, 22, (40,42,21,22), (37,39,64,65)⟩,(0,0,0,2))
theorem contact6 : PinContact.check pin6.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gU1
def pin7 : Pin × RegisterProduct.Hint := (⟨⟨false, false, true⟩, 27, 29, 47, 22, 21, 24, 26, 46, 22, (27,29,21,22), (24,26,46,47)⟩,(0,0,0,2))
theorem contact7 : PinContact.check pin7.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gU_right
def pin8 : Pin × RegisterProduct.Hint := (⟨⟨false, true, true⟩, 58, 56, 29, 20, 19, 62, 60, 28, 20, (56,58,19,20), (60,62,28,29)⟩,(0,0,0,2))
theorem contact8 : PinContact.check pin8.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gR0
def pin9 : Pin × RegisterProduct.Hint := (⟨⟨true, true, false⟩, 74, 72, 48, 52, 54, 76, 75, 49, 52, (52,54,72,74), (48,49,75,76)⟩,(0,0,0,2))
theorem contact9 : PinContact.check pin9.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gR1
def pin10 : Pin × RegisterProduct.Hint := (⟨⟨true, true, false⟩, 56, 54, 35, 52, 53, 58, 57, 36, 52, (52,53,54,56), (35,36,57,58)⟩,(0,1,1,3))
theorem contact10 : PinContact.check pin10.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gR2
def pin11 : Pin × RegisterProduct.Hint := (⟨⟨true, true, false⟩, 38, 36, 22, 52, 53, 40, 39, 23, 52, (52,53,36,38), (22,23,39,40)⟩,(0,1,1,3))
theorem contact11 : PinContact.check pin11.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gFin
def pin12 : Pin × RegisterProduct.Hint := (⟨⟨false, false, true⟩, 81, 83, 14, 12, 11, 79, 80, 13, 12, (81,83,11,12), (79,80,13,14)⟩,(0,0,0,0))
theorem contact12 : PinContact.check pin12.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gFinSide
def pin13 : Pin × RegisterProduct.Hint := (⟨⟨true, true, true⟩, 18, 16, 87, 85, 84, 27, 25, 86, 85, (84,85,16,18), (86,87,25,27)⟩,(0,0,0,0))
theorem contact13 : PinContact.check pin13.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- gFloor
def pin14 : Pin × RegisterProduct.Hint := (⟨⟨false, false, false⟩, 75, 77, 0, 25, 27, 73, 74, 1, 25, (75,77,25,27), (73,74,0,1)⟩,(0,0,0,0))
theorem contact14 : PinContact.check pin14.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- q
def pin15 : Pin × RegisterProduct.Hint := (⟨⟨false, false, false⟩, 63, 64, 6, 25, 27, 59, 61, 7, 25, (63,64,25,27), (59,61,6,7)⟩,(0,0,0,0))
theorem contact15 : PinContact.check pin15.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- r
def pin16 : Pin × RegisterProduct.Hint := (⟨⟨false, false, false⟩, 94, 95, 8, 25, 27, 90, 91, 9, 25, (94,95,25,27), (90,91,8,9)⟩,(0,0,0,0))
theorem contact16 : PinContact.check pin16.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- x
def pin17 : Pin × RegisterProduct.Hint := (⟨⟨false, false, false⟩, 67, 68, 4, 25, 27, 65, 66, 5, 25, (67,68,25,27), (65,66,4,5)⟩,(0,0,0,0))
theorem contact17 : PinContact.check pin17.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

-- z
def pin18 : Pin × RegisterProduct.Hint := (⟨⟨false, false, false⟩, 71, 72, 2, 25, 27, 69, 70, 3, 25, (71,72,25,27), (69,70,2,3)⟩,(0,0,0,0))
theorem contact18 : PinContact.check pin18.1 index.1 template.chart.cycle.points=true :=
  PinContact.check_of_edges edges_zip (by decide +kernel)

def pins : List (Pin × RegisterProduct.Hint) := [pin0, pin1, pin2, pin3, pin4, pin5, pin6, pin7, pin8, pin9, pin10, pin11, pin12, pin13, pin14, pin15, pin16, pin17, pin18]

theorem certificate : WingPinProof.Cert template cache boxes index pins where
  valid := by decide +kernel
  nodes := by decide +kernel
  contacts := (Bool.and_eq_true_iff.mpr ⟨contact0,(Bool.and_eq_true_iff.mpr ⟨contact1,(Bool.and_eq_true_iff.mpr ⟨contact2,(Bool.and_eq_true_iff.mpr ⟨contact3,(Bool.and_eq_true_iff.mpr ⟨contact4,(Bool.and_eq_true_iff.mpr ⟨contact5,(Bool.and_eq_true_iff.mpr ⟨contact6,(Bool.and_eq_true_iff.mpr ⟨contact7,(Bool.and_eq_true_iff.mpr ⟨contact8,(Bool.and_eq_true_iff.mpr ⟨contact9,(Bool.and_eq_true_iff.mpr ⟨contact10,(Bool.and_eq_true_iff.mpr ⟨contact11,(Bool.and_eq_true_iff.mpr ⟨contact12,(Bool.and_eq_true_iff.mpr ⟨contact13,(Bool.and_eq_true_iff.mpr ⟨contact14,(Bool.and_eq_true_iff.mpr ⟨contact15,(Bool.and_eq_true_iff.mpr ⟨contact16,(Bool.and_eq_true_iff.mpr ⟨contact17,(Bool.and_eq_true_iff.mpr ⟨contact18,rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  gaps := by decide +kernel
  assignments := by decide +kernel

theorem localized {ranks : List Nat} (size : ranks.length=3) (n j : Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈ranks,i≤n) :
    let s := (1:ℚ)/n
    WingPinProof.Forces template (s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)) :=
  WingPinProof.at_size (size ▸ WingBounds.Ordinary_40_200_520.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,records,certificate⟩ WingChart.Ordinary_40_200_520.axis_edges WingChart.Ordinary_40_200_520.indices cell_indices
    (WingFill.Ordinary_40_200_520.filled_eq size n j hn hj hr)

end ArtGallery.Orthogonal.BoundaryPoint.WingPins.Ordinary_40_200_520
end
