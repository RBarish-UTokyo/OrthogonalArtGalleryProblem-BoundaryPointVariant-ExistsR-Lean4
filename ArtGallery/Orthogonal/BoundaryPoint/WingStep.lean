module

public import ArtGallery.Orthogonal.BoundaryPoint.WingSeparation
public import ArtGallery.Orthogonal.BoundaryPoint.WingFence.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingFence.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingFence.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingFence.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingFence.Lower_10_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingFence.Lower_10_360_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingFence.Lower_10_520_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingFence.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.WingFence.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingFence.InvLe_1_360
public import ArtGallery.Orthogonal.BoundaryPoint.WingFence.InvLe_1_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingFence.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.WingFence.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingFence.InvRevGe_40_200

/-! # The sole possible high-step contact of each emitted wing -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingStep
open WingEnvelopeCert ChartDrawing HighStep DoorFenceCert ContourJoin BankCoordinates MarginCert
open CatalogPlan CatalogRanks CompiledSize CompiledAddresses WingSeparation

def Fenced (t : Template) (arity : Nat) : Prop := Cert t arity ∧ ∃ hints, check t hints=true

theorem catalogue : List.Forall₂ Fenced catalog arities := by
  apply List.Forall₂.cons (show Fenced _ _ from ⟨WingBounds.Ordinary_40_200_520.certificate,_,WingFence.Ordinary_40_200_520.checked⟩)
  apply List.Forall₂.cons (show Fenced _ _ from ⟨WingBounds.Shifted_40_200_520.certificate,_,WingFence.Shifted_40_200_520.checked⟩)
  apply List.Forall₂.cons (show Fenced _ _ from ⟨WingBounds.Lower_40_200_1000.certificate,_,WingFence.Lower_40_200_1000.checked⟩)
  apply List.Forall₂.cons (show Fenced _ _ from ⟨WingBounds.Lower_10_40_1000.certificate,_,WingFence.Lower_10_40_1000.checked⟩)
  apply List.Forall₂.cons (show Fenced _ _ from ⟨WingBounds.Lower_10_200_1000.certificate,_,WingFence.Lower_10_200_1000.checked⟩)
  apply List.Forall₂.cons (show Fenced _ _ from ⟨WingBounds.Lower_10_360_1000.certificate,_,WingFence.Lower_10_360_1000.checked⟩)
  apply List.Forall₂.cons (show Fenced _ _ from ⟨WingBounds.Lower_10_520_1000.certificate,_,WingFence.Lower_10_520_1000.checked⟩)
  apply List.Forall₂.cons (show Fenced _ _ from ⟨WingBounds.InvLe_1_40.certificate,_,WingFence.InvLe_1_40.checked⟩)
  apply List.Forall₂.cons (show Fenced _ _ from ⟨WingBounds.InvLe_1_200.certificate,_,WingFence.InvLe_1_200.checked⟩)
  apply List.Forall₂.cons (show Fenced _ _ from ⟨WingBounds.InvLe_1_360.certificate,_,WingFence.InvLe_1_360.checked⟩)
  apply List.Forall₂.cons (show Fenced _ _ from ⟨WingBounds.InvLe_1_520.certificate,_,WingFence.InvLe_1_520.checked⟩)
  apply List.Forall₂.cons (show Fenced _ _ from ⟨WingBounds.InvRevGe_1_10.certificate,_,WingFence.InvRevGe_1_10.checked⟩)
  apply List.Forall₂.cons (show Fenced _ _ from ⟨WingBounds.InvLe_40_200.certificate,_,WingFence.InvLe_40_200.checked⟩)
  apply List.Forall₂.cons (show Fenced _ _ from ⟨WingBounds.InvRevGe_40_200.certificate,_,WingFence.InvRevGe_40_200.checked⟩)
  exact List.Forall₂.nil

private theorem physical {t : Template} {rs : List Nat} (proof : Fenced t rs.length)
    (n j : Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n) {e : Entrance}
    (hit : (drawOne t n j rs).1=some e) :
    CoversLow (door j) (W n) ⟨e.2.map ratPoint⟩ := by
  obtain ⟨cert,hints,pass⟩ := proof
  let s := (1:ℚ)/n
  let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
  have pos : 0<getRat args 0 := by change (0:ℚ)<1/n; positivity
  have upper : (getRat args 0:ℝ)≤1/65 := by
    change ((1/(n:ℚ):ℚ):ℝ)≤1/65
    push_cast
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
  have trace := cyclic (args:=args) hints (parameters n j rs hn hj hr) cert.arithmetic pos upper pass
  have width : (1/320:ℚ)*getRat args 0=W n := by change (1/320:ℚ)*(1/n)=W n; unfold W; ring
  dsimp only at trace
  rw [width] at trace
  change (atDoor (door j) (W n) _).map (fun v => (door j,v))=some e at hit
  obtain ⟨path,output,rfl⟩ := Option.map_eq_some_iff.mp hit
  exact after_door trace output

private theorem selected {ts : List Template} {sz : List Nat} (all : List.Forall₂ Fenced ts sz)
    (n j tag : Nat) (rs : List Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n)
    (arity : sz[tag]?=some rs.length) {e : Entrance}
    (hit : (choose ts (fun t => drawOne t n j rs) tag (none,0)).1=some e) :
    CoversLow (door j) (W n) ⟨e.2.map ratPoint⟩ := by
  induction all generalizing tag with
  | nil => simp at arity
  | cons h _ ih =>
    cases tag with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at arity
      rw [arity] at h
      exact physical h n j hn hj hr hit
    | succ k =>
      simp only [List.getElem?_cons_succ] at arity
      exact ih k arity (by simpa [choose] using hit)

theorem sole_contact {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance}
    (path : WingSeparation.emitted eqs r j e) :
    CoversLow (door j) (W (scale eqs)) ⟨e.2.map ratPoint⟩ := by
  have nonempty : eqs≠[] := by intro z; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  have hr := List.fst_mem_of_mem_zipIdx path.1
  have ⟨v,a⟩ := CandidateTotal.valid_row hr
  have arity : arities[r.1]?=some (profileBanks r.1).length := by
    generalize hi : r.1=i at v ⊢; interval_cases i <;> rfl
  exact selected catalogue (scale eqs) j r.1 r.2 (scale_bounds nonempty).1
    (program_door eqs path.1).le (fun i hi => (program_ranks eqs hr hi).le) (a ▸ arity) path.2

end ArtGallery.Orthogonal.BoundaryPoint.WingStep
end
