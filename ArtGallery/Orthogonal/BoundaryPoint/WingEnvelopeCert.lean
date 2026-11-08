module

public import ArtGallery.Orthogonal.BoundaryPoint.WingEnvelope
public import ArtGallery.Orthogonal.BoundaryPoint.ChartDrawing

/-! # Bounding certificates for the catalogue of executed wing programs -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingEnvelopeCert
open ChartDrawing BoundaryChart MarginCert LinearRegister WingEnvelope BankCoordinates ContourJoin

def params (arity : Nat) : List Box := ⟨0,1/65⟩::List.replicate (arity+1) ⟨0,1⟩

structure Cert (t : Template) (arity : Nat) : Prop where
  arithmetic : ok (params arity) [] (t.corridor.baseRows++t.corridor.rest)=true
  x : stairOK t.corridor (stack [] (t.corridor.baseRows++t.corridor.rest)) false=true
  y : stairOK t.corridor (stack [] (t.corridor.baseRows++t.corridor.rest)) true=true
  rx : roomOK false t.room.x=true
  ry : roomOK true t.room.y=true

private theorem enclosed_ranks (n : Nat) (hn : 65≤n) (is : List Nat) (h : ∀ i∈is,i≤n) :
    Encloses (List.replicate is.length (⟨0,1⟩ : Box)) (is.map fun (i : Nat) => (i:ℝ)/n) := by
  induction is with
  | nil => exact empty_encloses
  | cons a l ih =>
    simp only [List.length_cons,List.replicate_succ,List.map_cons]
    exact Encloses.cons (normalized_index hn (h a List.mem_cons_self)) (ih (fun i hi => h i (List.mem_cons_of_mem _ hi)))

theorem parameters (n j : Nat) (rs : List Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n) :
    let s := (1:ℚ)/n
    let a := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    Encloses (params rs.length) (a.map ((↑) : ℚ → ℝ)) := by
  let s := (1:ℚ)/n
  let a := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
  have hb := Encloses.cons (reciprocal_size hn) ((enclosed_ranks n hn (j::rs))
    (by intro i hi; rcases List.mem_cons.mp hi with rfl|k; exact hj; exact hr _ k))
  have hparam : Encloses (params rs.length) (a.map ((↑) : ℚ → ℝ)) := by
    simpa [params,List.length_cons,a,s,Function.comp_def,div_eq_mul_inv] using hb
  exact hparam

theorem traced {t : Template} {n j : Nat} {rs : List Nat} (cert : Cert t rs.length)
    (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n) {e : Entrance} (hit : (drawOne t n j rs).1=some e) :
    e.1=door j ∧ ∀ q∈(Polygon.mk (e.2.map ratPoint)).filled,InStrip j q := by
  let s := (1:ℚ)/n
  let a := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
  have big : (65:ℚ)≤n := by exact_mod_cast hn
  have pos : (0:ℚ)<n := lt_of_lt_of_le (by norm_num) big
  have sp : 0<s := one_div_pos.mpr pos
  have su : s≤1/65 := one_div_le_one_div_of_le (by norm_num) big
  have hparam := parameters n j rs hn hj hr
  have stair := staircase hparam cert.arithmetic (by intro b; cases b; exact cert.x; exact cert.y)
  have full := merge stair (room t.room sp su cert.rx cert.ry)
  change (atDoor (door j) (W n) (t.chart.draw _)).map (fun p => (door j,p))=some e at hit
  obtain ⟨path,output,rfl⟩ := Option.map_eq_some_iff.mp hit
  refine ⟨rfl,fun q hq => enclosure (fun p hp => WingEnvelope.at_door output (fun u hu => drawn t.chart full hu) hp) hq⟩

end ArtGallery.Orthogonal.BoundaryPoint.WingEnvelopeCert
end
