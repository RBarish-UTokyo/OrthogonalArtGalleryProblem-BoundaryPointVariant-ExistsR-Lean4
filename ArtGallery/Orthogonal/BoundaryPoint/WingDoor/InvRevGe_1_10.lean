module

public import ArtGallery.Orthogonal.BoundaryPoint.DoorRead
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.InvRevGe_1_10

/-! Door detection for the actual rational coordinate program of this wing. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingDoor.InvRevGe_1_10
open MarginCert LinearRegister CorridorProgram DoorRead RectContour ContourJoin BankCoordinates
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def program := BankCorridor.InvRevGe_1_10.layout.baseRows++BankCorridor.InvRevGe_1_10.layout.rest

theorem checks : ok BankMargin.InvRevGe_1_10.params [] program=true := by
  apply ok_join BankMargin.InvRevGe_1_10.checked
  change ok BankMargin.InvRevGe_1_10.params (stack [] BankMargin.InvRevGe_1_10.construction) BankCorridor.InvRevGe_1_10.suffix=true
  unfold BankMargin.InvRevGe_1_10.construction
  simp only [stack_append]
  exact BankCorridor.InvRevGe_1_10.suffix_ok

theorem prefix_ok : check WingChart.InvRevGe_1_10.chart BankCorridor.InvRevGe_1_10.layout.cells program.reverse (stack [] program) 6=true := by decide +kernel

theorem opens (n j i0 i1 : Nat) (hn : 65≤n) (hj : j≤n) (hi0 : i0≤n) (hi1 : i1≤n)
    (extra : Data ℚ) :
    let s := (1:ℚ)/n
    let args := [s, ((j:ℚ)*s), ((i0:ℚ)*s), ((i1:ℚ)*s)]
    let g := BankCorridor.InvRevGe_1_10.layout.coords args
    (atDoor (door j) (W n) (WingChart.InvRevGe_1_10.chart.draw (g.1++extra.1,g.2++extra.2))).isSome=true := by
  let s := (1:ℚ)/n
  let args : List ℚ := [s, ((j:ℚ)*s), ((i0:ℚ)*s), ((i1:ℚ)*s)]
  have params : Encloses BankMargin.InvRevGe_1_10.params [1/(n:ℝ), ((j:ℝ)/n), ((i0:ℝ)/n), ((i1:ℝ)/n)] := Encloses.cons (reciprocal_size hn) (Encloses.cons (normalized_index hn hj) (Encloses.cons (normalized_index hn hi0) (Encloses.cons (normalized_index hn hi1) (empty_encloses))))
  have casted : args.map ((↑) : ℚ → ℝ)=[1/(n:ℝ), ((j:ℝ)/n), ((i0:ℝ)/n), ((i1:ℝ)/n)] := by simp [args,s,div_eq_mul_inv]
  have positive : 0<getRat args 0 := by change 0<(1:ℚ)/n; positivity
  have result := coordinate_open BankCorridor.InvRevGe_1_10.layout WingChart.InvRevGe_1_10.chart (args:=args) (casted ▸ params)
    positive checks prefix_ok extra (door j)
  have width : (1/320:ℚ)*getRat args 0=W n := by
    change (1/320:ℚ)*(1/n)=W n
    unfold W; ring
  rw [width] at result
  exact result

end ArtGallery.Orthogonal.BoundaryPoint.WingDoor.InvRevGe_1_10
end
