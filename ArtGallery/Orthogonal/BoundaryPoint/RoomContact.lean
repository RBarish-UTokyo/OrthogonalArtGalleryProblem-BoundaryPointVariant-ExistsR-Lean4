module

public import ArtGallery.Orthogonal.BoundaryPoint.GridParity

/-! # Two families of grid rectangles meeting exactly in one vertical window

On strictly increasing coordinate grids, every overlap of a rectangle of the
first family with a rectangle of the second family is decided by its grid
indices. A finite check that each overlap is empty or lies on the window,
and that one overlap is the whole window, identifies the intersection of the
two unions with the closed window segment. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomContact
open Set GridAtom GridParity CorridorProgram

/-- The index overlap of two rectangles. -/
def overlap (a b : Rect Nat) : Rect Nat :=
  (max a.1 b.1,min a.2.1 b.2.1,max a.2.2.1 b.2.2.1,min a.2.2.2 b.2.2.2)

/-- The window is the vertical index segment `x = w.1`, `w.2.1 ≤ y ≤ w.2.2`. -/
def inWindow (w : Nat × Nat × Nat) (r : Rect Nat) : Bool :=
  r.2.1<r.1 || r.2.2.2<r.2.2.1 || (r.1==w.1 && r.2.1==w.1 && decide (w.2.1≤r.2.2.1) && decide (r.2.2.2≤w.2.2))

def check (cs rs : List (Rect Nat)) (w : Nat × Nat × Nat) : Bool :=
  cs.all (fun c => rs.all fun r => inWindow w (overlap c r)) &&
  decide (w.2.1≤w.2.2) && cs.any (fun c => rs.any fun r => decide (overlap c r=(w.1,w.1,w.2.1,w.2.2)))

private theorem inBox_iff (X Y : Nat) (r : Rect Nat) :
    inBox X Y r=true ↔ line r.1≤X ∧ X≤line r.2.1 ∧ line r.2.2.1≤Y ∧ Y≤line r.2.2.2 := by
  simp [inBox]

private theorem line_inj {a b : Nat} : line a≤line b ↔ a≤b := by unfold line; omega

theorem contact {xs ys : List ℝ} (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    {cs rs : List (Rect Nat)}
    (hC : ∀ r ∈ cs, r.1<xs.length ∧ r.2.1<xs.length ∧ r.2.2.1<ys.length ∧ r.2.2.2<ys.length)
    (hR : ∀ r ∈ rs, r.1<xs.length ∧ r.2.1<xs.length ∧ r.2.2.1<ys.length ∧ r.2.2.2<ys.length)
    {w : Nat × Nat × Nat} (ok : check cs rs w=true) :
    cellsR xs ys cs ∩ cellsR xs ys rs =
      ArtGallery.segment (xs.getD w.1 0,ys.getD w.2.1 0) (xs.getD w.1 0,ys.getD w.2.2 0) := by
  simp only [check,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨all,ord⟩,c,hc,r,hr,eq⟩ := ok
  have wx : w.1<xs.length := by
    have := (hC c hc); have := (hR r hr); have h := congrArg (·.1) eq; simp only [overlap] at h; omega
  have wy0 : w.2.1<ys.length := by
    have := (hC c hc); have := (hR r hr); have h := congrArg (·.2.2.1) eq; simp only [overlap] at h; omega
  have wy1 : w.2.2<ys.length := by
    have := (hC c hc); have := (hR r hr); have h := congrArg (·.2.2.2) eq; simp only [overlap] at h; omega
  have vert : (xs.getD w.1 0,ys.getD w.2.1 0).1=(xs.getD w.1 0,ys.getD w.2.2 0).1 := rfl
  ext z
  rw [Set.mem_inter_iff,cells_iff hx hy hC,cells_iff hx hy hR,segment_box (Or.inl vert)]
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨⟨c,hc,bc⟩,⟨r,hr,br⟩⟩
    rw [inBox_iff] at bc br
    have h := all c hc r hr
    simp only [inWindow,overlap,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at h
    have ax := atom_bound z.1 xs
    rcases h with ((h|h)|⟨⟨⟨h1,h2⟩,h3⟩,h4⟩)
    · exfalso; simp only [line] at bc br; have h := of_decide_eq_true h; omega
    · exfalso; simp only [line] at bc br; have h := of_decide_eq_true h; omega
    · have h3 := of_decide_eq_true h3; have h4 := of_decide_eq_true h4
      have lx : line w.1≤atom z.1 xs := by simp only [line] at bc br ⊢; omega
      have ux : atom z.1 xs≤line w.1 := by simp only [line] at bc br ⊢; omega
      have ly : line w.2.1≤atom z.2 ys := by simp only [line] at bc br ⊢; omega
      have uy : atom z.2 ys≤line w.2.2 := by simp only [line] at bc br ⊢; omega
      have e1 := (line_le hx wx z.1).mpr lx
      have e2 := (le_line hx wx z.1).mpr ux
      have e3 := (line_le hy wy0 z.2).mpr ly
      have e4 := (le_line hy wy1 z.2).mpr uy
      exact ⟨Or.inl ⟨e1,e2⟩,Or.inl ⟨e3,e4⟩⟩
  · rintro ⟨bx,by'⟩
    have zx : z.1=xs.getD w.1 0 := by rcases bx with ⟨a,b⟩|⟨a,b⟩ <;> linarith
    have lx := (line_le hx wx z.1).mp zx.ge
    have ux := (le_line hx wx z.1).mp zx.le
    have e1 : max c.1 r.1=w.1 := congrArg Prod.fst eq
    have e2 : min c.2.1 r.2.1=w.1 := congrArg (·.2.1) eq
    have e3 : max c.2.2.1 r.2.2.1=w.2.1 := congrArg (·.2.2.1) eq
    have e4 : min c.2.2.2 r.2.2.2=w.2.2 := congrArg (·.2.2.2) eq
    have lo : line w.2.1≤line w.2.2 := line_inj.mpr ord
    have yin : line w.2.1≤atom z.2 ys ∧ atom z.2 ys≤line w.2.2 := by
      rcases by' with ⟨a,b⟩|⟨a,b⟩
      · exact ⟨(line_le hy wy0 z.2).mp a,(le_line hy wy1 z.2).mp b⟩
      · have a' := (line_le hy wy1 z.2).mp a
        have b' := (le_line hy wy0 z.2).mp b
        omega
    refine ⟨⟨c,hc,?_⟩,⟨r,hr,?_⟩⟩ <;> rw [inBox_iff] <;> simp only [line] at lx ux yin ⊢ <;> omega

end ArtGallery.Orthogonal.BoundaryPoint.RoomContact
end
