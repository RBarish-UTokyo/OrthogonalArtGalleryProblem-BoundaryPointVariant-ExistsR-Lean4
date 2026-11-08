module

public import ArtGallery.Orthogonal.BoundaryPoint.GridParity

/-! # Vertical slices of the exact parity and closed-rectangle tests
Only edges and cells incident with a slab are retained. A supplied slice is
checked once before its vertical positions are compared. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.GridSweep
open GridParity GridAtom RoomGrid CorridorProgram

abbrev Interval := Nat × Nat
abbrev Edge := Index × Index
structure Slice where
  walls : List Interval
  crossings : List Nat
  cells : List Interval

def allEdges (l : List Index) : List Edge := (List.range l.length).map fun i => (aidx l i,bidx l i)

def wall (X : Nat) (e : Edge) : Option Interval :=
  if Between (line e.1.1) (line e.2.1) X then some (line e.1.2,line e.2.2) else none
def crossing (X : Nat) (e : Edge) : Option Nat :=
  if (line e.1.1≤X ∧ X<line e.2.1) ∨ (line e.2.1≤X ∧ X<line e.1.1) then some (line e.1.2) else none
def tile (X : Nat) (r : Rect Nat) : Option Interval :=
  if line r.1≤X ∧ X≤line r.2.1 then some (line r.2.2.1,line r.2.2.2) else none

def slice (l : List Index) (rs : List (Rect Nat)) (X : Nat) : Slice :=
  let edges := allEdges l
  ⟨edges.filterMap (wall X),edges.filterMap (crossing X),rs.filterMap (tile X)⟩

def betweenTest (Y : Nat) (i : Interval) : Bool := decide (Between i.1 i.2 Y)
def boxTest (Y : Nat) (i : Interval) : Bool := decide (i.1 ≤ Y ∧ Y ≤ i.2)
def aboveTest (Y u : Nat) := decide (Y<u)
def correctAt (s : Slice) (Y : Nat) : Bool :=
  let k := s.crossings.countP (aboveTest Y)
  (s.walls.any (betweenTest Y) || decide ((k:ZMod 2)=1)) == s.cells.any (boxTest Y)
def correct (s : Slice) (ny : Nat) := (List.range (2*ny+1)).all (correctAt s)

private theorem wall_eval (E : List Edge) (X Y : Nat) :
    (E.filterMap (wall X)).any (betweenTest Y)=E.any (fun e => onEdge X Y e.1 e.2) := by
  induction E with
  | nil => rfl
  | cons e es ih =>
    by_cases h : Between (line e.1.1) (line e.2.1) X <;>
      simp only [List.filterMap_cons,wall,h,ite_true,ite_false,List.any_cons,ih,onEdge,betweenTest,true_and,
        false_and,decide_false,Bool.false_or]

private theorem cross_eval (E : List Edge) (X Y : Nat) :
    (E.filterMap (crossing X)).countP (aboveTest Y)=E.countP (fun e => cross X Y e.1 e.2) := by
  induction E with
  | nil => rfl
  | cons e es ih =>
    by_cases h : (line e.1.1≤X ∧ X<line e.2.1) ∨ (line e.2.1≤X ∧ X<line e.1.1) <;>
      simp [List.filterMap_cons,crossing,cross,h,List.countP_cons,aboveTest,ih]

private theorem cell_eval (rs : List (Rect Nat)) (X Y : Nat) :
    (rs.filterMap (tile X)).any (boxTest Y)=rs.any (inBox X Y) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    by_cases h : line r.1≤X ∧ X≤line r.2.1
    · simp [tile,List.filterMap_cons,h,inBox,boxTest,h.1,h.2,ih]
    · simp [tile,List.filterMap_cons,h,inBox,←and_assoc,ih]

private theorem sum_count (p : Nat → Bool) (n : Nat) :
    (∑ i ∈ Finset.range n, (if p i then (1:ZMod 2) else 0))=((List.range n).countP p:ZMod 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,List.range_succ,List.countP_append,ih]
    cases eq : p n <;> simp [eq]

theorem equivalent (l : List Index) (rs : List (Rect Nat)) (X ny : Nat) :
    rowOK l rs X ny=correct (slice l rs X) ny := by
  unfold rowOK correct
  apply List.all_congr rfl
  intro Y
  simp only [correctAt,slice,wall_eval,cross_eval,cell_eval,regionB,boundaryB,sumB,sum_count,
    allEdges,List.any_map,List.countP_map,Function.comp_def]

def sameSlice (a b : Slice) := a.walls==b.walls && a.crossings==b.crossings && a.cells==b.cells

private theorem slice_eq {a b : Slice} (pass : sameSlice a b=true) : a=b := by
  cases a; cases b; simpa only [sameSlice,Bool.and_eq_true,beq_iff_eq,Slice.mk.injEq,and_assoc] using pass

def step (l : List Index) (rs : List (Rect Nat)) (ny X : Nat) (pre : Slice) : Bool :=
  sameSlice (slice l rs X) pre && correct pre ny

theorem step_ok {l rs ny X s} (ok : step l rs ny X s=true) : rowOK l rs X ny=true := by
  have h : sameSlice (slice l rs X) s=true ∧ correct s ny=true := by simpa only [step,Bool.and_eq_true] using ok
  rw [equivalent,slice_eq h.1,h.2]

def block (l : List Index) (rs : List (Rect Nat)) (ny offset : Nat) (s : List Slice) :=
  s.zipIdx.all fun p => step l rs ny (offset+p.2) p.1

def Checked (l : List Index) (rs : List (Rect Nat)) (ny low high : Nat) :=
  ∀ i : Nat, low ≤ i → i < high → rowOK l rs i ny=true

theorem block_ok {l rs ny offset s} (h : block l rs ny offset s=true) :
    Checked l rs ny offset (offset+s.length) := by
  intro i lo hi
  have index : i-offset<s.length := by omega
  have member : (s[i-offset],i-offset)∈s.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem index)
  have good := List.all_eq_true.mp h _ member
  exact (show offset+(i-offset)=i by omega) ▸ step_ok good

theorem join {l rs ny a b c} (left : Checked l rs ny a b) (right : Checked l rs ny b c) : Checked l rs ny a c := by
  intro i lo hi; rcases lt_or_ge i b with h|h
  · exact left i lo h
  · exact right i h hi

/-! ## The same checks with the edge list built in one pass and a natural-number parity test

`allEdges l` reads both ends of every edge from the list (quadratic in the kernel); a declaration
proves once that it equals a list built in one pass (`l.zip (l.tail ++ l.take 1)`). -/

def sliceE (E : List Edge) (rs : List (Rect Nat)) (X : Nat) : Slice :=
  ⟨E.filterMap (wall X),E.filterMap (crossing X),rs.filterMap (tile X)⟩

def correctAtN (s : Slice) (Y : Nat) : Bool :=
  (s.walls.any (betweenTest Y) || Nat.beq (s.crossings.countP (aboveTest Y)%2) 1) == s.cells.any (boxTest Y)
def correctN (s : Slice) (ny : Nat) := (List.range (2*ny+1)).all (correctAtN s)

theorem parity2 (k : Nat) : decide ((k:ZMod 2)=1)=Nat.beq (k%2) 1 := by
  rw [←ZMod.natCast_mod k 2]
  have : k%2<2 := Nat.mod_lt _ (by norm_num)
  generalize k%2=m at this ⊢
  rcases (by omega : m=0 ∨ m=1) with rfl|rfl <;> rfl

theorem correctN_eq (s : Slice) (ny : Nat) : correctN s ny=correct s ny := by
  unfold correctN correct correctAtN correctAt; simp only [parity2]

def blockE (E : List Edge) (rs : List (Rect Nat)) (ny offset : Nat) (s : List Slice) :=
  s.zipIdx.all fun p => sameSlice (sliceE E rs (offset+p.2)) p.1 && correctN p.1 ny

theorem block_of_edges {l : List Index} {E : List Edge} (hE : allEdges l=E) {rs : List (Rect Nat)}
    {ny offset : Nat} {s : List Slice} (h : blockE E rs ny offset s=true) : block l rs ny offset s=true := by
  subst hE; unfold blockE at h; unfold block step
  simpa only [correctN_eq,sliceE,slice] using h

end ArtGallery.Orthogonal.BoundaryPoint.GridSweep
end
