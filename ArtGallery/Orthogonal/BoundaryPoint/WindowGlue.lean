module

public import Mathlib.Data.List.GetD
public import ArtGallery.Orthogonal.BoundaryPoint.SimplePaths
public import ArtGallery.Orthogonal.BoundaryPoint.WindowFill

/-! # Joining simple polygons meeting exactly along a common boundary edge
The hypotheses concern the input polygons. The output is the actual concatenation
of their complementary vertex paths. Its simplicity, closed filled union and
one-window attachment structure follow without any simplicity assumption on the output. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WindowGlue
open Set Geometry ArtGallery.Stade.Chain Jordan Existence

def whole (a b : Point) (u v : List Point) : Polygon := ⟨(a::u)++(b::v)⟩
def first (a b : Point) (u : List Point) : Polygon := ⟨(a::u)++[b]⟩

private theorem from_vertices {P Q : Polygon} (size : P.n=Q.n) (h : ∀ i, i<P.n → P.vtx i=Q.vtx i) : P=Q := by
  cases P with | mk p =>
    cases Q with | mk q =>
      have len : p.length=q.length := size
      congr 1
      apply List.ext_getElem len
      intro i hi hj
      have eq := h i hi
      change p.getD i (0,0)=q.getD i (0,0) at eq
      rwa [List.getD_eq_getElem (l:=p) (d:=(0,0)) hi,List.getD_eq_getElem (l:=q) (d:=(0,0)) hj] at eq

private theorem at_left (l r : List Point) {i : Nat} (h : i<l.length) :
    (l++r).getD i (0,0)=l.getD i (0,0) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left h]

private theorem at_right (l r : List Point) {i : Nat} (h : l.length ≤ i) :
    (l++r).getD i (0,0)=r.getD (i-l.length) (0,0) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right h]

private theorem first_arc (a b : Point) (u v : List Point) :
    (whole a b u v).arc 0 (a::u).length=first a b u := by
  let xs := a::u; let ys := b::v
  let P := whole a b u v
  have len : P.n=xs.length+ys.length := by simp [P,whole,xs,ys,Polygon.n]; omega
  have pos : 0<ys.length := Nat.zero_lt_succ _
  apply from_vertices
  · simp [first,Polygon.n,Polygon.arc]
  · intro i hi
    change i<(P.arc 0 xs.length).n at hi
    rw [n_arc] at hi
    have k : i≤xs.length := by omega
    change (P.arc 0 xs.length).vtx i=(first a b u).vtx i
    rw [vtx_arc P 0 xs.length k,Nat.zero_add,Nat.mod_eq_of_lt (by omega)]
    change (xs++ys).getD i (0,0)=(xs++[b]).getD i (0,0)
    rcases k.lt_or_eq with h|rfl
    · rw [at_left _ _ h,at_left _ _ h]
    · rw [at_right _ _ le_rfl,at_right _ _ le_rfl,Nat.sub_self]; rfl

private theorem second_arc (a b : Point) (u v : List Point) :
    (whole a b u v).arc (a::u).length (b::v).length=first b a v := by
  let xs := a::u; let ys := b::v; let P := whole a b u v
  have len : P.n=xs.length+ys.length := by simp [P,whole,xs,ys,Polygon.n]; omega
  apply from_vertices
  · simp [first,Polygon.n,Polygon.arc]
  · intro i hi
    change i<(P.arc xs.length ys.length).n at hi
    rw [n_arc] at hi
    have k : i≤ys.length := by omega
    change (P.arc xs.length ys.length).vtx i=(first b a v).vtx i
    rw [vtx_arc _ _ _ k]
    rcases k.lt_or_eq with h|rfl
    · rw [Nat.mod_eq_of_lt (by omega)]
      change (xs++ys).getD (xs.length+i) (0,0)=(ys++[a]).getD i (0,0)
      rw [at_right _ _ (Nat.le_add_right ..),Nat.add_sub_cancel_left,at_left _ _ h]
    · rw [← len,Nat.mod_self]
      change (xs++ys).getD 0 (0,0)=(ys++[a]).getD ys.length (0,0)
      rw [at_right _ _ le_rfl,Nat.sub_self]; rfl

theorem parity_splice (a b : Point) (u v : List Point) (z : Point) :
    parity (whole a b u v) z=Bool.xor (parity (first a b u) z) (parity (first b a v) z) := by
  let P := whole a b u v
  let m := (a::u).length; let k := (b::v).length
  have len : P.n=m+k := by simp [P,whole,Polygon.n,m,k]; omega
  have pos : 0<k := Nat.zero_lt_succ _
  have eq := parity_split P 0 m (by omega) z
  rw [Nat.zero_add,Nat.mod_eq_of_lt (by omega),show P.n-m=k by omega] at eq
  exact (first_arc a b u v ▸ second_arc a b u v ▸ eq)

theorem joined {a b z : Point} {u v : List Point}
    (hA : (first a b u).Simple) (hB : (first b a (v++[z])).Simple)
    (door : (first a b u).filled∩(first b a (v++[z])).filled=ArtGallery.segment a b) :
    let P := whole a b u (v++[z])
    let A := first a b u
    let B := first b a (v++[z])
    P.Simple ∧ P.filled=A.filled∪B.filled ∧
      WindowTree.Attachments A.filled P.filled ∧ WindowTree.Attachments B.filled P.filled := by
  let A := first a b u
  let B := first b a (v++[z])
  let P := whole a b u (v++[z])
  have Aopen := SimplePaths.open_simple hA
  have Bopen := SimplePaths.open_simple hB
  have form : ((b::v)++[z,a])=((b::(v++[z]))++[a]) := by simp [List.append_assoc]
  have contact : chainSet ((a::u)++[b])∩chainSet ((b::v)++[z,a]) ⊆ {a,b} := by
    rintro p ⟨pA,pB⟩
    rw [form] at pB
    have d : p∈A.filled∩B.filled := ⟨SimplePaths.trace_in pA,SimplePaths.trace_in pB⟩
    exact SimplePaths.closing hA ⟨door ▸ d,pA⟩
  have poly : P.Simple := by
    simpa only [P,whole,List.cons_append,List.append_assoc] using
      WindowSplice.simple Aopen (form ▸ Bopen) contact
  have meet : A.filled∩B.filled⊆A.boundary := door ▸ SimplePaths.door_in u
  have convex : Convex ℝ (A.filled∩B.filled) := door ▸ segment_convex a b
  have parityId := parity_splice a b u (v++[z])
  have filled := WindowFill.parity_union poly hA hB meet parityId
  refine ⟨poly,filled,WindowFill.attach poly hA hB meet convex parityId,?_⟩
  change WindowTree.Attachments B.filled P.filled
  rw [filled,Set.union_comm]
  apply WindowTree.Attachments.attach (.start (isClosed_filled B)) (isClosed_filled A)
  simpa only [Set.inter_comm B.filled A.filled] using convex

end ArtGallery.Orthogonal.BoundaryPoint.WindowGlue
end
