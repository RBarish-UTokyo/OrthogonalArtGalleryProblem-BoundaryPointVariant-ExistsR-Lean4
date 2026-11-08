module

public import ArtGallery.Orthogonal.BoundaryPoint.WingSeparation
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.Lower_10_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.Lower_10_360_1000
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.Lower_10_520_1000
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.InvLe_1_360
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.InvLe_1_520
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.CertifiedWing.InvRevGe_40_200

/-! # Hole-free Jordan boundaries for every executed wing of the generator -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RealizedWings
open WingOrderSound WingSeparation ChartDrawing ContourJoin CatalogPlan CatalogRanks CompiledSize CompiledAddresses

theorem catalogue : List.Forall₂ Evidence catalog arities := by
  apply List.Forall₂.cons CertifiedWing.Ordinary_40_200_520.evidence
  apply List.Forall₂.cons CertifiedWing.Shifted_40_200_520.evidence
  apply List.Forall₂.cons CertifiedWing.Lower_40_200_1000.evidence
  apply List.Forall₂.cons CertifiedWing.Lower_10_40_1000.evidence
  apply List.Forall₂.cons CertifiedWing.Lower_10_200_1000.evidence
  apply List.Forall₂.cons CertifiedWing.Lower_10_360_1000.evidence
  apply List.Forall₂.cons CertifiedWing.Lower_10_520_1000.evidence
  apply List.Forall₂.cons CertifiedWing.InvLe_1_40.evidence
  apply List.Forall₂.cons CertifiedWing.InvLe_1_200.evidence
  apply List.Forall₂.cons CertifiedWing.InvLe_1_360.evidence
  apply List.Forall₂.cons CertifiedWing.InvLe_1_520.evidence
  apply List.Forall₂.cons CertifiedWing.InvRevGe_1_10.evidence
  apply List.Forall₂.cons CertifiedWing.InvLe_40_200.evidence
  apply List.Forall₂.cons CertifiedWing.InvRevGe_40_200.evidence
  exact List.Forall₂.nil

private theorem selected {ts : List Template} {sz : List Nat} (all : List.Forall₂ Evidence ts sz)
    (n j tag : Nat) (rs : List Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n)
    (arity : sz[tag]?=some rs.length) {e : Entrance}
    (hit : (choose ts (fun t => drawOne t n j rs) tag (none,0)).1=some e) :
    (Polygon.mk (e.2.map ratPoint)).Simple := by
  induction all generalizing tag with
  | nil => simp at arity
  | cons h _ ih =>
    cases tag with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at arity
      rw [arity] at h
      exact WingOrderSound.emitted h n j hn hj hr hit
    | succ k =>
      simp only [List.getElem?_cons_succ] at arity
      exact ih k arity (by simpa [choose] using hit)

theorem simple {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance}
    (path : WingSeparation.emitted eqs r j e) : (Polygon.mk (e.2.map ratPoint)).Simple := by
  have nonempty : eqs≠[] := by intro z; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  have hr := List.fst_mem_of_mem_zipIdx path.1
  have ⟨v,a⟩ := CandidateTotal.valid_row hr
  have arity : arities[r.1]?=some (profileBanks r.1).length := by
    generalize hi : r.1=i at v ⊢; interval_cases i <;> rfl
  exact selected catalogue (scale eqs) j r.1 r.2 (scale_bounds nonempty).1
    (program_door eqs path.1).le (fun i hi => (program_ranks eqs hr hi).le) (a ▸ arity) path.2

end ArtGallery.Orthogonal.BoundaryPoint.RealizedWings
end
