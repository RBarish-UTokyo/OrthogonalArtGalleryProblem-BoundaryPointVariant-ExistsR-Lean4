module

public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.RegCertT
public import ArtGallery.Orthogonal.BoundaryPoint.RowTree.InvLe_40_200

/-! The register rows and boxes of profile `InvLe_40_200` as balanced index trees (generated), so that
register certificates are decided with logarithmic lookups (`out_eq`, `check_eq`). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RowLit.InvLe_40_200
open MarginCert RegCert RegChain
set_option maxRecDepth 200000

abbrev rT := RowTree.InvLe_40_200.rT
abbrev bT := RowTree.InvLe_40_200.bT

theorem rT_eq : rT=ZSign.ITree.ofList (WingOrder.InvLe_40_200.rows.map some) := RowTree.InvLe_40_200.rT_eq

theorem bT_eq : bT=ZSign.ITree.ofList WingOrder.InvLe_40_200.boxes := RowTree.InvLe_40_200.bT_eq

theorem out_eq (c bl bh : ℚ) (ins : Inputs) (known : List (Nat × KronCert.Ex × KronCert.Ex)) (st : Step) :
    st.out c bl bh WingOrder.InvLe_40_200.rows WingOrder.InvLe_40_200.boxes ins known=
      RegCertT.outT c bl bh (fun i => rT.get none i) (fun i => bT.get zeroBox i) ins known st := by
  rw [← RegCertT.tree_rows _ _ rT_eq,← RegCertT.tree_boxes _ _ bT_eq,RegCertT.outT_eq]

theorem check_eq (ins : Inputs) (known : List (Nat × KronCert.Ex × KronCert.Ex)) (es : List RegCert.Entry) :
    RegCert.check WingOrder.InvLe_40_200.rows WingOrder.InvLe_40_200.boxes ins known es=
      RegCertT.checkT (fun i => rT.get none i) (fun i => bT.get zeroBox i) ins known es := by
  rw [← RegCertT.tree_rows _ _ rT_eq,← RegCertT.tree_boxes _ _ bT_eq,RegCertT.checkT_eq]

end ArtGallery.Orthogonal.BoundaryPoint.RowLit.InvLe_40_200
end
