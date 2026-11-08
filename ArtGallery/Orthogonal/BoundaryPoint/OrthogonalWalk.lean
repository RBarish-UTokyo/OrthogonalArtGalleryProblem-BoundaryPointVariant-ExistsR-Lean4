module

public import ArtGallery.Orthogonal.BoundaryPoint.ChartDrawing
public import Mathlib.Data.List.Chain

/-! # Orthogonality under removal of a wing door and insertion into a hub edge -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.OrthogonalWalk
open RectContour ContourJoin

def aligned (p q : Vertex) : Prop := p.1=q.1 ∨ p.2=q.2

def loop : List Vertex → Prop
  | [] => True
  | a::l => ((a::l)++[a]).IsChain aligned

private theorem index_loop (l : List Vertex) :
    loop l ↔ ∀ (i : Nat) (hi : i<l.length), aligned l[i] (l[(i+1) % l.length]'(Nat.mod_lt _ (by omega))) := by
  cases l with
  | nil => simp [loop]
  | cons a t =>
    let l := a::t
    have positive : 0<l.length := by simp [l]
    change (l++[a]).IsChain aligned ↔ _
    rw [List.isChain_iff_getElem]
    have eq (i : Nat) (hi : i<l.length) :
        (l++[a])[i+1]'(by simp; omega)= (l[(i+1) % l.length]'(Nat.mod_lt _ positive)) := by
      by_cases h : i+1<l.length
      · simp only [List.getElem_append_left h,Nat.mod_eq_of_lt h]
      · have e : i+1=l.length := by omega
        simp [e,l,List.getElem_append_right]
    constructor
    · intro h i hi
      change i<l.length at hi
      have pair := h i (by simp only [List.length_append,List.length_singleton]; omega)
      rwa [List.getElem_append_left hi,eq _ hi] at pair
    · intro h i hi
      have bound : i<l.length := by simpa using hi
      rw [List.getElem_append_left bound,eq _ bound]
      exact h i bound

theorem polygon (l : List Vertex) : loop l ↔ (Polygon.mk (l.map ratPoint)).Orthogonal := by
  rw [index_loop]
  let P : Polygon := ⟨l.map ratPoint⟩
  have n : P.n=l.length := by simp [P,Polygon.n]
  have atPos (i : Nat) (hi : i<l.length) : P.vtx i=ratPoint l[i] := by
    change (l.map ratPoint).getD i (0,0)=_
    rw [List.getD_eq_getElem (l:=l.map ratPoint) (d:=(0,0)) (by simpa using hi),List.getElem_map]
  constructor
  · intro h i hi
    change i<P.n at hi; rw [n] at hi
    change (P.vtx i).1=(P.vtx ((i+1)%P.n)).1 ∨ (P.vtx i).2=(P.vtx ((i+1)%P.n)).2
    rw [n,atPos i hi,atPos _ (Nat.mod_lt _ (by omega))]
    simpa only [aligned,ratPoint,Rat.cast_inj] using h i hi
  · intro h i hi
    have he := h i (show i<P.n by simpa only [n] using hi)
    change (P.vtx i).1=(P.vtx ((i+1)%P.n)).1 ∨ (P.vtx i).2=(P.vtx ((i+1)%P.n)).2 at he
    rw [n,atPos _ hi,atPos _ (Nat.mod_lt _ (by omega))] at he
    simpa only [aligned,ratPoint,Rat.cast_inj] using he

theorem parts {l : List Vertex} (h : loop l) :
    l.IsChain aligned ∧ ∀ a∈l.getLast?, ∀ b∈l.head?, aligned a b := by
  cases l with
  | nil => simp
  | cons a l =>
    have k := List.isChain_append.mp h
    refine ⟨k.1,?_⟩
    intro x hx b hb
    have eq : a=b := by simpa using hb
    exact k.2.2 _ hx b (by simpa using eq)

structure Level (y : ℚ) (l : List Vertex) : Prop where
  path : l.IsChain aligned
  first : ∀ a∈l.head?, a.2=y
  last : ∀ a∈l.getLast?, a.2=y

private theorem mem_or {α : Type} {w z : Option α} {t : α} (ht : t∈w.or z) : t∈w ∨ t∈z := by
  cases w <;> simp_all

theorem level_nil (y : ℚ) : Level y [] := ⟨by simp,by simp,by simp⟩
theorem level_single (v : Vertex) : Level v.2 [v] := by
  constructor <;> simp_all

theorem Level.append {y : ℚ} {l r : List Vertex} (hl : Level y l) (hr : Level y r) : Level y (l++r) := by
  constructor
  · exact hl.path.append hr.path (fun a ha b hb => Or.inr ((hl.last _ ha).trans (hr.first _ hb).symm))
  · intro a ha
    rw [List.head?_append] at ha
    exact (mem_or ha).elim (hl.first _) (hr.first _)
  · intro a ha
    rw [List.getLast?_append] at ha
    exact (mem_or ha).elim (hr.last _) (hl.last _)

theorem level_flat {α : Type} (y : ℚ) (l : List α) (f : α → List Vertex)
    (h : ∀ a∈l,Level y (f a)) : Level y (l.flatMap f) := by
  induction l with
  | nil => exact level_nil y
  | cons a l ih => exact (h _ List.mem_cons_self).append (ih (fun i hi => h _ (List.mem_cons_of_mem _ hi)))

theorem at_door {l out : List Vertex} {d w : ℚ} (h : loop l) (hit : atDoor d w l=some out) : Level 1 out := by
  let i := l.idxOf (0,1)
  have ⟨chain,seam⟩ := parts h
  unfold atDoor at hit
  dsimp only at hit
  split at hit
  · contradiction
  next hclear =>
    have H : ¬((decide (i ≥ l.length) || (l.getD ((i+1) % l.length) (0,0) != (w,1))) = true) := hclear
    have hi : i<l.length := by by_contra! k; simp [k] at H
    have succPoint : l.getD ((i+1) % l.length) (0,0)=(w,1) := by
      simpa only [Nat.not_le.mpr hi,decide_false,Bool.false_or,bne_iff_ne,not_not] using H
    obtain rfl := Option.some.inj hit
    let ls := l.drop (i+1); let rs := l.take (i+1)
    let shift := fun p : Vertex => (p.1+d,p.2)
    have old : l[i]=(0,1) := List.getElem_idxOf hi
    have rotated : (ls++rs).IsChain aligned := by
      apply (chain.drop _).append (chain.take _)
      intro a ha b hb
      change a∈(l.drop (i+1)).getLast? at ha
      rw [List.getLast?_drop] at ha
      split at ha
      · contradiction
      · apply seam a ha b
        simpa [rs,List.head?_take] using hb
    have lastR : rs.getLast?=some (0,1) := by
      simp only [rs,List.getLast?_take,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel,
        List.getElem?_eq_getElem hi,Option.some_or,old]
    have firstLR : (ls++rs).head?=some (w,1) := by
      rw [List.head?_append]
      by_cases k : i+1<l.length
      · have pos : l[i+1]=(w,1) := by
          rw [Nat.mod_eq_of_lt k,List.getD_eq_getElem (l:=l) (d:=(0,0)) k] at succPoint
          exact succPoint
        simp [ls,List.getElem?_eq_getElem k,pos]
      · have eq : i+1=l.length := by omega
        have ne : l≠[] := by intro f; simp [f] at hi
        have z : 0<l.length := List.length_pos_iff.mpr ne
        have pos : l[0]=(w,1) := by simpa only [eq,Nat.mod_self,List.getD_eq_getElem (l:=l) (d:=(0,0)) z] using succPoint
        simp [ls,rs,eq,List.head?_eq_getElem?,List.getElem?_eq_getElem z,pos]
    change Level 1 ((ls++rs).map shift)
    constructor
    · apply List.isChain_map_of_isChain _ _ rotated
      intro a b edge
      rcases edge with x|y
      · exact Or.inl (congrArg (·+d) x)
      · exact Or.inr y
    · intro a ha
      rw [List.head?_map,firstLR] at ha
      have eq : shift (w,1)=a := by simpa using ha
      rw [← eq]
    · intro a ha
      rw [List.getLast?_map,List.getLast?_append,lastR] at ha
      have eq : shift (0,1)=a := by simpa using ha
      rw [← eq]

end ArtGallery.Orthogonal.BoundaryPoint.OrthogonalWalk
end
