module

public import ArtGallery.Orthogonal.BoundaryPoint.RegCert
public import ArtGallery.Orthogonal.BoundaryPoint.PolyBox

/-! # Closed forms through `max` and absolute-value rows

On the parameter box the branch of a `larger` or `absVal` row is fixed: a
certified sign of the difference of the two argument closed forms (or of the
argument itself) selects the argument whose closed form the register takes. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RegBranch
open MarginCert LinearRegister RegisterTable KronCert PolyBox RegCert

/-- Multiplication by a sign, as an expression. -/
def esc (σ : Int) (e : Ex) : Ex := .mul (.lit [[[σ]]]) e

theorem esc_ev (σ : Int) (e : Ex) (x y z : ℝ) : (esc σ e).ev x y z=σ*e.ev x y z := by
  simp [esc,Ex.ev,ev3,ev2,ev1]

/-- The sign certificate of a `larger` row choosing the first argument (`first`) or the second.
The cross difference `M = Na*Db - Nb*Da` is supplied and checked by a Kronecker identity, so the
kernel never multiplies the closed forms symbolically. -/
def larger (c bl bh : ℚ) (Na Da Nb Db M : Ex) (σa σb : Int) : Bool :=
  decide (σa=1 ∨ σa=-1) && decide (σb=1 ∨ σb=-1) &&
  signPos c bl bh σa Da && signPos c bl bh σb Db &&
  auto (.sub M (.sub (.mul Na Db) (.mul Nb Da))) &&
  (auto M || signPos c bl bh (σa*σb) M)

private theorem sq_sign {σ : Int} (h : σ=1 ∨ σ=-1) : (σ:ℝ)*σ=1 := by
  rcases h with rfl|rfl <;> norm_num

/-- `va ≥ vb` from certified signs of the closed forms. -/
theorem ge_of_signs {va vb : ℝ} {Na Da Nb Db : Ex} {x y z : ℝ}
    (ha : va*Da.ev x y z=Na.ev x y z) (hb : vb*Db.ev x y z=Nb.ev x y z)
    {c bl bh : ℚ} (B : Box c bl bh x y z) {σa σb : Int} {M : Ex} (h : larger c bl bh Na Da Nb Db M σa σb=true) :
    vb≤va := by
  simp only [larger,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨sa,sb⟩,pa⟩,pb⟩,km⟩,pc⟩ := h
  have hM := Ex.sound km x y z
  simp only [Ex.ev] at hM
  have pa' := signPos_sound B pa; have pb' := signPos_sound B pb
  have e : (σa:ℝ)*σb*(va*Da.ev x y z*Db.ev x y z-vb*Db.ev x y z*Da.ev x y z)=
      (va-vb)*((σa*Da.ev x y z)*(σb*Db.ev x y z)) := by ring
  have hMv : M.ev x y z=va*Da.ev x y z*Db.ev x y z-vb*Db.ev x y z*Da.ev x y z := by
    rw [←ha,←hb] at hM; linarith
  have prod := mul_pos pa' pb'
  rcases pc with kz|pc
  · -- equal arguments
    have hz := Ex.sound kz x y z
    have h0 : (va-vb)*((σa*Da.ev x y z)*(σb*Db.ev x y z))=0 := by
      rw [← e,← hMv,hz,mul_zero]
    have := (mul_eq_zero.mp h0).resolve_right prod.ne'
    linarith
  · have pc' := signPos_sound B pc
    rw [hMv] at pc'
    push_cast at pc'
    rw [e] at pc'
    have := pos_of_mul_pos_left pc' prod.le
    linarith

/-- A `larger` row takes the closed form of its first argument. -/
theorem holds_larger {args xs : List ℚ} {rows : List Row} (run : Ledger args rows xs) {i a b : Nat}
    (hop : (rows[i]?).map Row.op=some (.larger a b)) {x y z : ℝ} {Na Da Nb Db : Ex}
    (ha : Holds xs x y z (i+1+a) Na Da) (hb : Holds xs x y z (i+1+b) Nb Db)
    {c bl bh : ℚ} (B : Box c bl bh x y z) {σa σb : Int} {M : Ex} (h : larger c bl bh Na Da Nb Db M σa σb=true) :
    Holds xs x y z i Na Da := by
  have le := ge_of_signs ha.1 hb.1 B h
  obtain ⟨r,hr,e⟩ := Option.map_eq_some_iff.mp hop
  have v := original run hr
  rw [e] at v
  simp only [Op.rat,drop_lookup] at v
  have : getRat xs i=getRat xs (i+1+a) := by
    rw [v]; apply max_eq_left; exact_mod_cast le
  rw [Holds,this]; exact ha

/-- A `larger` row takes the closed form of its second argument. -/
theorem holds_larger' {args xs : List ℚ} {rows : List Row} (run : Ledger args rows xs) {i a b : Nat}
    (hop : (rows[i]?).map Row.op=some (.larger a b)) {x y z : ℝ} {Na Da Nb Db : Ex}
    (ha : Holds xs x y z (i+1+a) Na Da) (hb : Holds xs x y z (i+1+b) Nb Db)
    {c bl bh : ℚ} (B : Box c bl bh x y z) {σa σb : Int} {M : Ex} (h : larger c bl bh Nb Db Na Da M σb σa=true) :
    Holds xs x y z i Nb Db := by
  have le := ge_of_signs hb.1 ha.1 B h
  obtain ⟨r,hr,e⟩ := Option.map_eq_some_iff.mp hop
  have v := original run hr
  rw [e] at v
  simp only [Op.rat,drop_lookup] at v
  have : getRat xs i=getRat xs (i+1+b) := by
    rw [v]; apply max_eq_right; exact_mod_cast le
  rw [Holds,this]; exact hb

/-- The sign certificate of an `absVal` row: `σ*N*D>0` on the box, with the product `M = N*D`
supplied and checked by a Kronecker identity. -/
def absSign (c bl bh : ℚ) (N D M : Ex) (σ : Int) : Bool :=
  decide (σ=1 ∨ σ=-1) &&
    ((decide (σ=1) && auto N) || (auto (.sub M (.mul N D)) && signPos c bl bh σ M))

theorem holds_abs {args xs : List ℚ} {rows : List Row} (run : Ledger args rows xs) {i a : Nat}
    (hop : (rows[i]?).map Row.op=some (.absVal a)) {x y z : ℝ} {N D : Ex}
    (ha : Holds xs x y z (i+1+a) N D)
    {c bl bh : ℚ} (B : Box c bl bh x y z) {σ : Int} {M : Ex} (h : absSign c bl bh N D M σ=true) :
    Holds xs x y z i (esc σ N) D := by
  simp only [absSign,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h
  obtain ⟨sg,⟨s1,kz⟩|⟨km,p⟩⟩ := h
  · -- the argument is identically zero, and so is its absolute value
    have hN := Ex.sound kz x y z
    obtain ⟨r,hr,e⟩ := Option.map_eq_some_iff.mp hop
    have v := original run hr
    rw [e] at v
    simp only [Op.rat,drop_lookup] at v
    have va0 : ((getRat xs (i+1+a) : ℚ) : ℝ)=0 := by
      have h1 := ha.1; rw [hN] at h1
      exact (mul_eq_zero.mp h1).resolve_right ha.2
    have vi : ((getRat xs i : ℚ) : ℝ)=0 := by
      rw [v]; push_cast; rw [va0,abs_zero]
    refine ⟨?_,ha.2⟩
    rw [vi,esc_ev,hN]; ring
  have hM := Ex.sound km x y z
  simp only [Ex.ev] at hM
  have p' := signPos_sound B p
  rw [show M.ev x y z=N.ev x y z*D.ev x y z by linarith,←ha.1] at p'
  obtain ⟨r,hr,e⟩ := Option.map_eq_some_iff.mp hop
  have v := original run hr
  rw [e] at v
  simp only [Op.rat,drop_lookup] at v
  set va : ℝ := ((getRat xs (i+1+a) : ℚ) : ℝ)
  have hD := ha.2
  have sq : (0:ℝ)<D.ev x y z*D.ev x y z := mul_self_pos.mpr hD
  -- σ*va*D^2 > 0, so σ*va > 0
  have pv : (0:ℝ)<σ*va := by
    have : (σ:ℝ)*(va*D.ev x y z*D.ev x y z)=(σ*va)*(D.ev x y z*D.ev x y z) := by ring
    rw [this] at p'; exact pos_of_mul_pos_left p' sq.le
  have habs : ((getRat xs i : ℚ) : ℝ)=σ*va := by
    rw [v]; push_cast
    rcases sg with rfl|rfl
    · simp at pv ⊢; exact abs_of_pos pv
    · simp at pv ⊢; rw [abs_of_neg (by linarith)]
  refine ⟨?_,hD⟩
  rw [habs,esc_ev,←ha.1]; ring

end ArtGallery.Orthogonal.BoundaryPoint.RegBranch
end
