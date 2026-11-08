module

public import ArtGallery.Orthogonal.BoundaryPoint.CopySpec
public import ArtGallery.Orthogonal.BoundaryPoint.WingModel

/-! # Emitted role records from the joined chart data

The role records of a template are the role part of its joined chart data; when that data is the
index data read on the grid (`WingModel.good_at_size`), the records are the index records read on
the grid. Proved once for an abstract template, so that no profile unfolds its data. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRecords
open ChartDrawing BoundaryChart IndexedWing CorridorProgram

theorem of_join {t : Template} {idx : Data Nat} {n j : Nat} {rs : List Nat}
    (eq : ShapeRefs.join (t.corridor.coords ((1:ℚ)/n::((j:ℚ)*((1:ℚ)/n))::(rs.map fun (i:Nat) => (i:ℚ)*((1:ℚ)/n))))
        (t.room.coords ((1:ℚ)/n))=
      WingEnvelope.mapData
        (fun i => (grid t ((1:ℚ)/n::((j:ℚ)*((1:ℚ)/n))::(rs.map fun (i:Nat) => (i:ℚ)*((1:ℚ)/n))) false).getD i 0)
        (fun i => (grid t ((1:ℚ)/n::((j:ℚ)*((1:ℚ)/n))::(rs.map fun (i:Nat) => (i:ℚ)*((1:ℚ)/n))) true).getD i 0) idx) :
    GlobalPins.records t n j rs=idx.2.map (fun l => l.map fun p =>
      ((grid t ((1:ℚ)/n::((j:ℚ)*((1:ℚ)/n))::(rs.map fun (i:Nat) => (i:ℚ)*((1:ℚ)/n))) false).getD p.1 0,
       (grid t ((1:ℚ)/n::((j:ℚ)*((1:ℚ)/n))::(rs.map fun (i:Nat) => (i:ℚ)*((1:ℚ)/n))) true).getD p.2 0)) := by
  have := congrArg Prod.snd eq
  simpa [GlobalPins.records,ShapeRefs.join,WingEnvelope.mapData] using this

end ArtGallery.Orthogonal.BoundaryPoint.CopyRecords
end
