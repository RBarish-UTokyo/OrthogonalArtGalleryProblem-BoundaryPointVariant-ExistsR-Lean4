module

public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.RegCertT
public import ArtGallery.Orthogonal.BoundaryPoint.RowTree.Ordinary_40_200_520

/-! The register rows and boxes of profile `Ordinary_40_200_520` as balanced index trees (generated), so that
register certificates are decided with logarithmic lookups (`out_eq`, `check_eq`). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RowLit.Ordinary_40_200_520
open MarginCert RegCert RegChain
set_option maxRecDepth 200000

abbrev rT := RowTree.Ordinary_40_200_520.rT
abbrev bT := RowTree.Ordinary_40_200_520.bT

theorem rT_eq : rT=ZSign.ITree.ofList (WingOrder.Ordinary_40_200_520.rows.map some) := RowTree.Ordinary_40_200_520.rT_eq

theorem bT_eq : bT=ZSign.ITree.ofList WingOrder.Ordinary_40_200_520.boxes := RowTree.Ordinary_40_200_520.bT_eq

theorem out_eq (c bl bh : ℚ) (ins : Inputs) (known : List (Nat × KronCert.Ex × KronCert.Ex)) (st : Step) :
    st.out c bl bh WingOrder.Ordinary_40_200_520.rows WingOrder.Ordinary_40_200_520.boxes ins known=
      RegCertT.outT c bl bh (fun i => rT.get none i) (fun i => bT.get zeroBox i) ins known st := by
  rw [← RegCertT.tree_rows _ _ rT_eq,← RegCertT.tree_boxes _ _ bT_eq,RegCertT.outT_eq]

theorem check_eq (ins : Inputs) (known : List (Nat × KronCert.Ex × KronCert.Ex)) (es : List RegCert.Entry) :
    RegCert.check WingOrder.Ordinary_40_200_520.rows WingOrder.Ordinary_40_200_520.boxes ins known es=
      RegCertT.checkT (fun i => rT.get none i) (fun i => bT.get zeroBox i) ins known es := by
  rw [← RegCertT.tree_rows _ _ rT_eq,← RegCertT.tree_boxes _ _ bT_eq,RegCertT.checkT_eq]

end ArtGallery.Orthogonal.BoundaryPoint.RowLit.Ordinary_40_200_520
end
