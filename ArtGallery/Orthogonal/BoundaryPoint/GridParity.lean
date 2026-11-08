module

public import ArtGallery.Orthogonal.BoundaryPoint.GridAtom
public import ArtGallery.Orthogonal.BoundaryPoint.CorridorProgram

/-! # Certified inside/outside lookup for an orthogonal grid cycle

Membership in the closed region of a simple orthogonal polygon, including
its boundary, depends only on the two grid atoms of the target. This is a
specialization of the preserved Jordan parity theorem. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.GridParity

open Set RoomGrid GridAtom CorridorProgram ArtGallery.Orthogonal.Hard
open scoped BigOperators

def Between {α} [LE α] (u v z : α) : Prop := (u≤z ∧ z≤v) ∨ (v≤z ∧ z≤u)
instance {α} [LE α] [DecidableLE α] (u v z : α) : Decidable (Between u v z) := by unfold Between; infer_instance

private theorem interp {a b t : ℝ} (ht : 0≤t) (ht' : t≤1) : Between a b (a+t*(b-a)) := by
  rcases le_total a b with h|h
  · exact Or.inl ⟨by linarith [mul_nonneg ht (sub_nonneg.mpr h)],
      by linarith [mul_le_mul_of_nonneg_right ht' (sub_nonneg.mpr h)]⟩
  · exact Or.inr ⟨by linarith [mul_le_mul_of_nonpos_right ht' (sub_nonpos.mpr h)],
      by linarith [mul_nonpos_of_nonneg_of_nonpos ht (sub_nonpos.mpr h)]⟩

theorem segment_box {a b z : Point} (h : a.1=b.1 ∨ a.2=b.2) :
    z ∈ segment a b ↔ Between a.1 b.1 z.1 ∧ Between a.2 b.2 z.2 := by
  constructor
  · rintro ⟨t,ht,ht',rfl⟩
    exact ⟨interp ht ht',interp ht ht'⟩
  · rintro ⟨hx,hy⟩
    rcases h with h|h
    · have hz : z.1=a.1 := by rcases hx with a|b <;> linarith
      rcases hy with ⟨hl,hu⟩|⟨hl,hu⟩
      · exact Jordan.mem_segment_of_vertical h hz hl hu
      · rw [Geometry.segment_comm]
        exact Jordan.mem_segment_of_vertical h.symm (hz.trans h) hl hu
    · have hz : z.2=a.2 := by rcases hy with a|b <;> linarith
      rcases hx with ⟨hl,hu⟩|⟨hl,hu⟩
      · exact GridPins.horizontal h hz hl hu
      · rw [Geometry.segment_comm]
        exact GridPins.horizontal h.symm (hz.trans h) hl hu

private theorem cross_horiz {a b z : Point} (h : a.2=b.2) (hd : a.1<b.1) :
    Jordan.crosses z a b ↔ a.1≤z.1 ∧ z.1<b.1 ∧ z.2<a.2 := by
  rw [Jordan.crosses_iff_of_lt hd,← h,sub_self,zero_mul]
  have hp := sub_pos.mpr hd
  constructor
  · rintro ⟨hl,hu,hc⟩
    refine ⟨hl,hu,?_⟩
    by_contra! hn
    exact (not_le_of_gt hc) (mul_nonneg (sub_nonneg.mpr hn) hp.le)
  · rintro ⟨hl,hu,hc⟩
    exact ⟨hl,hu,mul_neg_of_neg_of_pos (sub_neg.mpr hc) hp⟩

theorem crossing {a b z : Point} (h : a.1=b.1 ∨ a.2=b.2) :
    Jordan.crosses z a b ↔ ((a.1≤z.1 ∧ z.1<b.1) ∨ (b.1≤z.1 ∧ z.1<a.1)) ∧ z.2<a.2 := by
  rcases h with hx|hy
  · have hn := Jordan.not_crosses_of_eq (z := z) hx
    have ht : ¬ (a.1≤z.1 ∧ z.1<b.1) := by rintro ⟨_,_⟩; linarith
    have hu : ¬ (b.1≤z.1 ∧ z.1<a.1) := by rintro ⟨_,_⟩; linarith
    simp [hn,ht,hu]
  · rcases lt_trichotomy a.1 b.1 with hab|hab|hab
    · rw [cross_horiz hy hab]
      have hn : ¬ (b.1≤z.1 ∧ z.1<a.1) := by rintro ⟨_,_⟩; linarith
      tauto
    · have hn := Jordan.not_crosses_of_eq (z := z) hab
      have ht : ¬ (a.1≤z.1 ∧ z.1<b.1) := by rintro ⟨_,_⟩; linarith
      have hu : ¬ (b.1≤z.1 ∧ z.1<a.1) := by rintro ⟨_,_⟩; linarith
      simp [hn,ht,hu]
    · rw [Jordan.crosses_comm,cross_horiz hy.symm hab,← hy]
      have hn : ¬ (a.1≤z.1 ∧ z.1<b.1) := by rintro ⟨_,_⟩; linarith
      tauto

def onEdge (X Y : Nat) (a b : Index) : Bool :=
  decide (Between (line a.1) (line b.1) X ∧ Between (line a.2) (line b.2) Y)
def cross (X Y : Nat) (a b : Index) : Bool :=
  decide ((((line a.1 ≤ X ∧ X < line b.1) ∨ (line b.1 ≤ X ∧ X < line a.1))) ∧ Y < line a.2)
def aidx (l : List Index) (i : Nat) := l.getD i (0,0)
def bidx (l : List Index) (i : Nat) := l.getD ((i+1)%l.length) (0,0)

def boundaryB (l : List Index) (X Y : Nat) : Bool :=
  (List.range l.length).any (fun i => onEdge X Y (aidx l i) (bidx l i))
def sumB (l : List Index) (X Y : Nat) : ZMod 2 :=
  ∑ i ∈ Finset.range l.length, if cross X Y (aidx l i) (bidx l i) then 1 else 0
def regionB (l : List Index) (X Y : Nat) := boundaryB l X Y || decide (sumB l X Y=1)

def inBox (X Y : Nat) (r : Rect Nat) : Bool :=
  decide (line r.1 ≤ X ∧ X ≤ line r.2.1 ∧ line r.2.2.1 ≤ Y ∧ Y ≤ line r.2.2.2)

def cellsR (xs ys : List ℝ) (rs : List (Rect Nat)) : Set Point :=
  {z | ∃ r ∈ rs, xs.getD r.1 0 ≤ z.1 ∧ z.1 ≤ xs.getD r.2.1 0 ∧
    ys.getD r.2.2.1 0 ≤ z.2 ∧ z.2 ≤ ys.getD r.2.2.2 0}

theorem cells_iff {xs ys : List ℝ} (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    {rs : List (Rect Nat)} (hR : ∀ r ∈ rs, r.1<xs.length ∧ r.2.1<xs.length ∧
      r.2.2.1<ys.length ∧ r.2.2.2<ys.length) (z : Point) :
    z ∈ cellsR xs ys rs ↔ rs.any (inBox (atom z.1 xs) (atom z.2 ys)) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨r,hr,a,b,c,d⟩
    have h := hR r hr
    exact ⟨r,hr,decide_eq_true ⟨(line_le hx h.1 _).1 a,(le_line hx h.2.1 _).1 b,
      (line_le hy h.2.2.1 _).1 c,(le_line hy h.2.2.2 _).1 d⟩⟩
  · rintro ⟨r,hr,hb⟩
    have h := hR r hr
    obtain ⟨a,b,c,d⟩ := of_decide_eq_true hb
    exact ⟨r,hr,(line_le hx h.1 _).2 a,(le_line hx h.2.1 _).2 b,
      (line_le hy h.2.2.1 _).2 c,(le_line hy h.2.2.2 _).2 d⟩

theorem edge_tests {xs ys : List ℝ} (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    {l : List Index} (hV : ∀ p ∈ l, p.1<xs.length ∧ p.2<ys.length) (ho : cyclicAxis l)
    (z : Point) (i : Nat) (hi : i<l.length) :
    let P := Polygon.mk (l.map (gridPt xs ys))
    let X := atom z.1 xs; let Y := atom z.2 ys
    (z ∈ P.edge i ↔ onEdge X Y (aidx l i) (bidx l i)=true) ∧
    (Jordan.crosses z (P.vtx i) (P.vtx ((i+1)%P.n)) ↔ cross X Y (aidx l i) (bidx l i)=true) := by
  let f := gridPt xs ys
  let P : Polygon := ⟨l.map f⟩
  let X := atom z.1 xs; let Y := atom z.2 ys
  have hn : P.n=l.length := by simp [P,Polygon.n]
  have atI (i : Nat) (hi : i<l.length) : P.vtx i=f (aidx l i) := by
    change (l.map f).getD i (0,0) = f (l.getD i (0,0))
    rw [List.getD_eq_getElem (l := l.map f) (d := (0,0)) (by simpa using hi),
        List.getD_eq_getElem (l := l) (d := (0,0)) hi,List.getElem_map]
  change (z ∈ P.edge i ↔ onEdge X Y (aidx l i) (bidx l i)=true) ∧
    (Jordan.crosses z (P.vtx i) (P.vtx ((i+1)%P.n)) ↔ cross X Y (aidx l i) (bidx l i)=true)
  let j := (i+1)%l.length
  have hj : j<l.length := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hi)
  have ha := hV l[i] (List.getElem_mem hi)
  have hb := hV l[j] (List.getElem_mem hj)
  let u := l[i]; let v := l[j]
  have axis : (f u).1=(f v).1 ∨ (f u).2=(f v).2 := by
    rcases ho ⟨i,hi⟩ with h|h
    · exact Or.inl (congrArg (fun k => xs.getD k 0) h)
    · exact Or.inr (congrArg (fun k => ys.getD k 0) h)
  have ua : aidx l i = u := List.getD_eq_getElem (l := l) (d := (0,0)) hi
  have vb : bidx l i = v := List.getD_eq_getElem (l := l) (d := (0,0)) hj
  have pv : P.vtx ((i+1)%P.n)=f v := by
    rw [hn]
    exact (atI j hj).trans (congrArg f vb)
  rw [Polygon.edge, pv, (atI i hi).trans (congrArg f ua), ua,vb]
  change u.1<xs.length ∧ u.2<ys.length at ha
  change v.1<xs.length ∧ v.2<ys.length at hb
  constructor
  · rw [segment_box axis, onEdge, decide_eq_true_eq]
    dsimp only [Between, f, gridPt, X, Y]
    rw [line_le hx ha.1, line_le hx hb.1, le_line hx ha.1, le_line hx hb.1,
        line_le hy ha.2, line_le hy hb.2, le_line hy ha.2, le_line hy hb.2]
  · rw [crossing axis, cross, decide_eq_true_eq]
    dsimp only [f, gridPt, X, Y]
    rw [line_le hx ha.1, line_le hx hb.1, (compare_line hx ha.1 _).1,
        (compare_line hx hb.1 _).1, (compare_line hy ha.2 _).1]

theorem boundary_iff {xs ys : List ℝ} (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    {l : List Index} (hV : ∀ p ∈ l, p.1<xs.length ∧ p.2<ys.length) (ho : cyclicAxis l) (z : Point) :
    z ∈ (Polygon.mk (l.map (gridPt xs ys))).boundary ↔ boundaryB l (atom z.1 xs) (atom z.2 ys)=true := by
  simp only [boundaryB,List.any_eq_true,List.mem_range,Polygon.boundary,Set.mem_ofPred_eq,Polygon.n,List.length_map]
  exact exists_congr (fun i => ⟨fun ⟨h,m⟩ => ⟨h,(edge_tests hx hy hV ho z i h).1.mp m⟩,
    fun ⟨h,m⟩ => ⟨h,(edge_tests hx hy hV ho z i h).1.mpr m⟩⟩)

theorem region_iff {xs ys : List ℝ} (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    {l : List Index} (hV : ∀ p ∈ l, p.1<xs.length ∧ p.2<ys.length) (ho : cyclicAxis l)
    (hs : (Polygon.mk (l.map (gridPt xs ys))).Simple) (z : Point) :
    z ∈ (Polygon.mk (l.map (gridPt xs ys))).filled ↔ regionB l (atom z.1 xs) (atom z.2 ys)=true := by
  let f := gridPt xs ys
  let P : Polygon := ⟨l.map f⟩
  let X := atom z.1 xs; let Y := atom z.2 ys
  have hn : P.n=l.length := by simp [P,Polygon.n]
  have hboundary : z ∈ P.boundary ↔ boundaryB l X Y = true := boundary_iff hx hy hV ho z
  have hsum : Jordan.crossSum P z = sumB l X Y := by
    simp only [Jordan.crossSum,sumB,hn]
    apply Finset.sum_congr rfl
    intro i hi
    have h := (edge_tests hx hy hV ho z i (Finset.mem_range.mp hi)).2
    change (Jordan.crosses z (P.vtx i) (P.vtx ((i+1)%P.n)) ↔ cross X Y (aidx l i) (bidx l i)=true) at h
    rw [hn] at h
    simp only [Jordan.crossInd,h]
  change z ∈ P.filled ↔ (boundaryB l X Y || decide (sumB l X Y=1)) = true
  simp only [Bool.or_eq_true,decide_eq_true_eq,← hboundary,← hsum]
  by_cases hb : z∈P.boundary
  · exact iff_of_true (Or.inl hb) (Or.inl hb)
  · rw [Jordan.mem_filled_iff hs hb, Jordan.parity_eq_true_iff]
    tauto

def rowOK (l : List Index) (rs : List (Rect Nat)) (X ny : Nat) : Bool :=
  (List.range (2*ny+1)).all fun Y => regionB l X Y == rs.any (inBox X Y)

theorem filled_of_rows {xs ys : List ℝ} (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    {l : List Index} (hV : ∀ p ∈ l, p.1<xs.length ∧ p.2<ys.length) (ho : cyclicAxis l)
    (hs : (Polygon.mk (l.map (gridPt xs ys))).Simple)
    {rs : List (Rect Nat)} (hR : ∀ r ∈ rs, r.1<xs.length ∧ r.2.1<xs.length ∧
      r.2.2.1<ys.length ∧ r.2.2.2<ys.length)
    (h : ∀ i : Fin (2*xs.length+1), rowOK l rs i.val ys.length=true) :
    (Polygon.mk (l.map (gridPt xs ys))).filled = cellsR xs ys rs := by
  ext z
  rw [region_iff hx hy hV ho hs z,cells_iff hx hy hR z]
  let i : Fin (2*xs.length+1) := ⟨atom z.1 xs,by have := atom_bound z.1 xs; omega⟩
  have hX := h i
  have hY : atom z.2 ys ∈ List.range (2*ys.length+1) :=
    List.mem_range.mpr (Nat.lt_succ_of_le (atom_bound z.2 ys))
  have hb := beq_iff_eq.mp (List.all_eq_true.mp hX _ hY)
  exact Iff.of_eq (congrArg (· = true) hb)

end ArtGallery.Orthogonal.BoundaryPoint.GridParity
end
