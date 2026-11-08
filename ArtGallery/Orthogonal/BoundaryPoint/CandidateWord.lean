module

public import ArtGallery.Orthogonal.BoundaryPoint.ChartDrawing
public import ArtGallery.Orthogonal.BoundaryPoint.ContourJoin
public import ArtGallery.PTime.INVCode
public import ArtGallery.PTime.AGPDecode
public import ArtGallery.Orthogonal.Spec

/-! # Candidate word map from bounded ETR-INV to the gallery specification

Each local boundary cycle loses its horizontal door. Its complementary
boundary path is spliced into the high edge of the shared hub. A malformed
source or a failed contour returns the empty word. Geometric correctness of
this total candidate map is proved separately at the verified stages.
-/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CandidateWord
open Complexity PhysicalLayout SourcePortPlan PlanGeometry RectContour CorridorProgram

def pathAtDoor (d w : ℚ) (rs : List (Rect ℚ)) : Option (List Vertex) := do
  let cycle ← boundary rs
  ContourJoin.atDoor d w cycle

/-- Independent rectangle-union implementation used to verify the compact turn charts. -/
def tracedVertices (Φ : List ETRINV.Constraint) : Option (List Vertex × Nat) := do
  if Φ.isEmpty then return ([(0,0),(1,0),(1,1),(0,1)],1)
  let g := generate Φ
  let hubCycle ← boundary g.commonRoom
  let w := BankCoordinates.W (PhysicalLayout.size Φ)
  let wings ← g.entrances.mapM fun (d,rs) => do return (d,← pathAtDoor d w rs)
  let joined ← ContourJoin.splice w hubCycle wings
  return (joined,g.budget)

def vertices (Φ : List ETRINV.Constraint) : Option (List Vertex × Nat) :=
  ChartDrawing.vertices (CatalogPlan.compile Φ)

def pack (p : Vertex) : FracPoint := ⟨p.1.num,p.1.den,p.2.num,p.2.den⟩

def word (w : Word) : Word :=
  match ETRINV.decodeINV w with
  | none => []
  | some Φ => match vertices Φ with
    | none => []
    | some (v,g) => encodeAGP (v.map pack) g

theorem pack_valid (p : Vertex) : (pack p).Valid := ⟨p.1.den_pos,p.2.den_pos⟩

theorem pack_point (p : Vertex) : (pack p).toPoint = ratPoint p := by
  simp only [pack,FracPoint.toPoint,ratPoint,Rat.cast_def]

theorem word_of_output {Φ : List ETRINV.Constraint} {v g}
    (h : vertices Φ = some (v,g)) : word (ETRINV.encode Φ) = encodeAGP (v.map pack) g := by
  simp [word,ETRINV.decodeINV_encode,h]

theorem word_bad_input {w : Word} (h : ETRINV.decodeINV w = none) : word w=[] := by simp [word,h]

end ArtGallery.Orthogonal.BoundaryPoint.CandidateWord
end
