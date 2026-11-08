module

public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrderSound

/-! The realized, translated polygon of this profile is simple at every input size. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.InvLe_40_200
open WingOrderSound WingOrder.InvLe_40_200 ChartDrawing ContourJoin

theorem evidence : Evidence template 2 :=
  ⟨WingBounds.InvLe_40_200.certificate,WingChart.InvLe_40_200.checked,WingChart.InvLe_40_200.indices,
    cache,xHints,yHints,sizes,verified,x_ok,y_ok⟩

theorem simple {rs : List Nat} (size : rs.length=2) (n j : Nat) (hn : 65≤n)
    (hj : j≤n) (hr : ∀ i∈rs,i≤n) {e : Entrance} (h : (drawOne template n j rs).1=some e) :
    (Polygon.mk (e.2.map ratPoint)).Simple := emitted (size ▸ evidence) n j hn hj hr h

end ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.InvLe_40_200
end
