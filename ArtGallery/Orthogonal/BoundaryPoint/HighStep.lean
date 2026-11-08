module

public import ArtGallery.Orthogonal.BoundaryPoint.InsideDoor
public import ArtGallery.Orthogonal.BoundaryPoint.ContourJoin

/-! # The part of an executed wing that can meet its hub step
At or below the high step, a downward ray can escape the wing unless its
initial point lies on the door itself. This uses the definition of the
Jordan-filled set and also applies before simplicity has been established. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HighStep
open RectContour ContourJoin Geometry Set

def PairOK (w : ℚ) (a b : Vertex) : Prop :=
  ((1101/10:ℚ)<a.1 ∧ (1101/10:ℚ)<b.1) ∨ (1<a.2 ∧ 1<b.2) ∨
  ((0≤a.1 ∧ a.1≤w ∧ 1≤a.2) ∧ (0≤b.1 ∧ b.1≤w ∧ 1≤b.2))

def Wall (d w : ℝ) (p : Point) : Prop :=
  d+1101/10<p.1 ∨ 1<p.2 ∨ (d≤p.1 ∧ p.1≤d+w ∧ 1≤p.2)

def Mouth (d w : ℝ) (p : Point) : Prop := p.2=1 ∧ d≤p.1 ∧ p.1≤d+w

def CoversLow (d w : ℝ) (P : Polygon) : Prop :=
  ∀ p∈P.filled,p.1≤d+1101/10 → p.2≤1 → Mouth d w p

theorem downward {P : Polygon} {d w : ℝ} (wall : ∀ p∈P.boundary, Wall d w p) : CoversLow d w P := by
  intro p hp hx hy
  by_contra miss
  have clear (t : ℝ) (ht : 0≤t) : p + t • ((0,-1):Point) ∉ P.boundary := by
    intro h
    have entry := wall _ h
    simp only [Wall,Geometry.add_fst,Geometry.add_snd,Geometry.smul_fst,Geometry.smul_snd,
      mul_zero,add_zero,mul_neg,mul_one] at entry
    rcases entry with right|above|⟨L,R,B⟩
    · linarith
    · linarith
    · exact miss ⟨by linarith,L,R⟩
  have outside : p∉P.boundary := by simpa using clear 0 (le_refl _)
  exact Jordan.not_isBoundedSet_connectedComponentIn_of_ray P (d:=(0,-1)) (by simp)
    (by rintro _ ⟨t,ht,rfl⟩; exact clear t ht) ((Jordan.mem_filled_iff_bounded P outside).mp hp)

theorem interpolated (a b : ℝ) {t : ℝ} (h : 0≤t) (H : t≤1) :
    min a b≤a+t*(b-a) ∧ a+t*(b-a)≤max a b := by
  rcases le_total a b with le|le
  · rw [min_eq_left le,max_eq_right le]
    constructor <;> nlinarith only [mul_nonneg h (sub_nonneg.mpr le),mul_nonneg (sub_nonneg.mpr H) (sub_nonneg.mpr le)]
  · rw [min_eq_right le,max_eq_left le]
    constructor <;> nlinarith only [mul_nonneg h (sub_nonneg.mpr le),mul_nonneg (sub_nonneg.mpr H) (sub_nonneg.mpr le)]

def moved (d : ℚ) (v : Vertex) : Point := ratPoint (v.1+d,v.2)

theorem side {a b : Vertex} {d w : ℚ} (safe : PairOK w a b) {q : Point}
    (h : q∈ArtGallery.segment (moved d a) (moved d b)) : Wall d w q := by
  obtain ⟨t,ht,hu,rfl⟩ := mem_segment_iff_lerp.mp h
  have x := interpolated (moved d a).1 (moved d b).1 ht hu
  have y := interpolated (moved d a).2 (moved d b).2 ht hu
  simp only [moved,ratPoint,Rat.cast_add] at x y
  simp only [Wall,lerp_fst,lerp_snd,moved,ratPoint,Rat.cast_add]
  rcases safe with A|B|⟨A,B⟩
  · left
    have a' : (1101/10:ℝ)<a.1 := by simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_lt (K:=ℝ)).mpr A.1
    have b' : (1101/10:ℝ)<b.1 := by simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_lt (K:=ℝ)).mpr A.2
    exact lt_of_lt_of_le (lt_min (by linarith) (by linarith)) x.1
  · right; left; exact (lt_min (by exact_mod_cast B.1) (by exact_mod_cast B.2)).trans_le y.1
  · right; right
    have A' : (0:ℝ)≤a.1 ∧ (a.1:ℝ)≤w ∧ (1:ℝ)≤a.2 := by exact_mod_cast A
    have B' : (0:ℝ)≤b.1 ∧ (b.1:ℝ)≤w ∧ (1:ℝ)≤b.2 := by exact_mod_cast B
    exact ⟨(le_min (by linarith [A'.1]) (by linarith [B'.1])).trans x.1,
      x.2.trans (max_le (by linarith [A'.2.1]) (by linarith [B'.2.1])),
      (le_min A'.2.2 B'.2.2).trans y.1⟩

def Cyclic (w : ℚ) (l : List Vertex) : Prop := ∀ i, i<l.length →
  PairOK w (l.getD i (0,0)) (l.getD ((i+1)%l.length) (0,0))

theorem shifted {d w : ℚ} {l : List Vertex} (bound : Cyclic w l) :
    CoversLow d w ⟨l.map (moved d)⟩ := by
  apply downward
  intro q h
  obtain ⟨i,hi,edge⟩ := h
  let P : Polygon := ⟨l.map (moved d)⟩
  have size : P.n=l.length := by simp [P,Polygon.n]
  change i<P.n at hi
  change q∈ArtGallery.segment (P.vtx i) (P.vtx ((i+1)%P.n)) at edge
  rw [size] at hi edge
  have vertex (j : Nat) (hj : j<l.length) : P.vtx j=moved d (l.getD j (0,0)) := by
    change (l.map (moved d)).getD j (0,0)=_
    rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map,List.getD_eq_getElem _ _ hj]
  rw [vertex _ hi,vertex _ (Nat.mod_lt _ (by omega))] at edge
  exact side (bound i hi) edge

theorem after_door {d w : ℚ} {l path : List Vertex} (ok : Cyclic w l) (out : atDoor d w l=some path) :
    CoversLow d w ⟨path.map ratPoint⟩ := by
  let i := l.idxOf (0,1)
  unfold atDoor at out
  dsimp only at out
  split at out
  · contradiction
  next notMissing =>
    have bound : i+1≤l.length := by
      have h : ¬(i≥l.length ∨ (l.getD ((i+1)%l.length) (0,0) != (w,1))=true) := by
        simpa only [i,Bool.or_eq_true,decide_eq_true_eq] using notMissing
      omega
    obtain rfl := Option.some.inj out
    change CoversLow d w ⟨((l.drop (i+1)++l.take (i+1)).map _).map ratPoint⟩
    rw [←List.rotate_eq_drop_append_take bound,List.map_map]
    change CoversLow d w ⟨(l.rotate (i+1)).map (moved d)⟩
    rw [List.map_rotate,←InsideDoor.rotate_list]
    simpa only [CoversLow,Existence.filled_rotate] using shifted (d:=d) ok

end ArtGallery.Orthogonal.BoundaryPoint.HighStep
end
