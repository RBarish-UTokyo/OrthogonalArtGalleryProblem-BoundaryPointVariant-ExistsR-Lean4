module

public import ArtGallery.Orthogonal.BoundaryPoint.CandidateTotal
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Lower_10_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Lower_10_360_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.Lower_10_520_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.InvLe_1_360
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.InvLe_1_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingBounds.InvRevGe_40_200

/-! # Disjointness of the actual filled wings at distinct source rows
Each entry in the batch is the rotated, translated path that the hub splice
uses. Its filled polygon stays in a closed strip of width 1520. Consecutive
door origins are 2000 units apart. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingSeparation
open CatalogPlan CatalogRanks CompiledSize CompiledAddresses ChartDrawing ContourJoin
open WingEnvelope WingEnvelopeCert BankCoordinates

def arities : List Nat := [3,3,3,3,3,3,3,2,2,2,2,2,2,2]

theorem catalogue : List.Forall₂ Cert catalog arities := by
  apply List.Forall₂.cons WingBounds.Ordinary_40_200_520.certificate
  apply List.Forall₂.cons WingBounds.Shifted_40_200_520.certificate
  apply List.Forall₂.cons WingBounds.Lower_40_200_1000.certificate
  apply List.Forall₂.cons WingBounds.Lower_10_40_1000.certificate
  apply List.Forall₂.cons WingBounds.Lower_10_200_1000.certificate
  apply List.Forall₂.cons WingBounds.Lower_10_360_1000.certificate
  apply List.Forall₂.cons WingBounds.Lower_10_520_1000.certificate
  apply List.Forall₂.cons WingBounds.InvLe_1_40.certificate
  apply List.Forall₂.cons WingBounds.InvLe_1_200.certificate
  apply List.Forall₂.cons WingBounds.InvLe_1_360.certificate
  apply List.Forall₂.cons WingBounds.InvLe_1_520.certificate
  apply List.Forall₂.cons WingBounds.InvRevGe_1_10.certificate
  apply List.Forall₂.cons WingBounds.InvLe_40_200.certificate
  apply List.Forall₂.cons WingBounds.InvRevGe_40_200.certificate
  exact List.Forall₂.nil

private theorem lookup_arity {tag : Nat} (h : tag<14) :
    arities[tag]?=some (profileBanks tag).length := by interval_cases tag <;> rfl

private theorem selected {ts : List Template} {sizes : List Nat} (all : List.Forall₂ Cert ts sizes)
    (n j tag : Nat) (rs : List Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n)
    (arity : sizes[tag]?=some rs.length) {e : Entrance}
    (hit : (choose ts (fun t => drawOne t n j rs) tag (none,0)).1=some e) :
    e.1=door j ∧ ∀ q∈(Polygon.mk (e.2.map ratPoint)).filled,InStrip j q := by
  induction all generalizing tag with
  | nil => simp at arity
  | cons h _ ih =>
    cases tag with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at arity
      rw [arity] at h
      exact traced h hn hj hr hit
    | succ k =>
      simp only [List.getElem?_cons_succ] at arity
      exact ih k arity (by simpa [choose] using hit)

def emitted (eqs : List ETRINV.Constraint) (r : CatalogPlan.Row) (j : Nat) (e : Entrance) : Prop :=
  (r,j)∈(compile eqs).1.zipIdx ∧
    (choose catalog (fun t => drawOne t (scale eqs) j r.2) r.1 (none,0)).1=some e

theorem placement {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance}
    (path : emitted eqs r j e) :
    e.1=door j ∧ ∀ q∈(Polygon.mk (e.2.map ratPoint)).filled,InStrip j q := by
  have nonempty : eqs≠[] := by
    intro z; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  have hr := List.fst_mem_of_mem_zipIdx path.1
  have ⟨v,a⟩ := CandidateTotal.valid_row hr
  exact selected catalogue (scale eqs) j r.1 r.2 (scale_bounds nonempty).1
    (program_door eqs path.1).le (fun i hi => (program_ranks eqs hr hi).le)
    (a ▸ lookup_arity v) path.2

theorem disjoint {eqs : List ETRINV.Constraint} {r s : CatalogPlan.Row} {j k : Nat} {a b : Entrance}
    (left : emitted eqs r j a) (right : emitted eqs s k b) (different : j≠k) :
    Disjoint (Polygon.mk (a.2.map ratPoint)).filled (Polygon.mk (b.2.map ratPoint)).filled := by
  exact Set.disjoint_left.mpr (fun _ ha hb => separate different ((placement left).2 _ ha) ((placement right).2 _ hb))

end ArtGallery.Orthogonal.BoundaryPoint.WingSeparation
end
