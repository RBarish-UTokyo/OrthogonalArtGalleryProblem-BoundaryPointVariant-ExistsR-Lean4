module

public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrderSound

/-! The realized, translated polygon of this profile is simple at every input size. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.Lower_10_40_1000
open WingOrderSound WingOrder.Lower_10_40_1000 ChartDrawing ContourJoin

theorem evidence : Evidence template 3 :=
  ⟨WingBounds.Lower_10_40_1000.certificate,WingChart.Lower_10_40_1000.checked,WingChart.Lower_10_40_1000.indices,
    cache,xHints,yHints,sizes,verified,x_ok,y_ok⟩

theorem simple {rs : List Nat} (size : rs.length=3) (n j : Nat) (hn : 65≤n)
    (hj : j≤n) (hr : ∀ i∈rs,i≤n) {e : Entrance} (h : (drawOne template n j rs).1=some e) :
    (Polygon.mk (e.2.map ratPoint)).Simple := emitted (size ▸ evidence) n j hn hj hr h

end ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.Lower_10_40_1000
end
