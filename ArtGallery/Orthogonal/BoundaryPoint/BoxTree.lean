module

public import ArtGallery.Orthogonal.BoundaryPoint.RegisterTable

/-! # Register boxes with logarithmic lookup

`RegisterTable.atomBox` reads a box from a list, which the kernel walks one cell at a time. The
same boxes stored in a balanced binary tree (index `0` at the root, odd indices on the left, even
positive indices on the right) are read in logarithmically many steps; `fastBox` agrees with
`atomBox` everywhere. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.BoxTree
open MarginCert RegisterTable

inductive Tree where
  | nil
  | node (v : Box) (l r : Tree)

mutual
/-- The elements at even positions. -/
def evens : List Box → List Box
  | [] => []
  | x::xs => x::odds xs
/-- The elements at odd positions. -/
def odds : List Box → List Box
  | [] => []
  | _::xs => evens xs
end

def Tree.ofListF : Nat → List Box → Tree
  | 0,_ => .nil
  | _,[] => .nil
  | f+1,x::xs => .node x (Tree.ofListF f (evens xs)) (Tree.ofListF f (odds xs))

def Tree.ofList (bs : List Box) : Tree := Tree.ofListF bs.length bs

def Tree.get : Tree → Nat → Box
  | .nil,_ => zeroBox
  | .node v _ _,0 => v
  | .node _ l r,i+1 => if i%2=0 then l.get (i/2) else r.get (i/2)

/-- The boxes of the register atoms, read from the tree. -/
def fastBox (bs : List Box) : Nat → Box
  | 0 => ⟨1,1⟩
  | i+1 => (Tree.ofList bs).get i

theorem split_get : ∀ l : List Box, (∀ k, (evens l)[k]?=l[2*k]?) ∧ (∀ k, (odds l)[k]?=l[2*k+1]?) ∧
    (evens l).length≤l.length ∧ (odds l).length≤l.length
  | [] => by simp [evens,odds]
  | x::xs => by
    obtain ⟨e,o,le,lo⟩ := split_get xs
    refine ⟨?_,?_,?_,?_⟩
    · intro k
      cases k with
      | zero => simp [evens]
      | succ k => rw [evens,List.getElem?_cons_succ,o k,show 2*(k+1)=(2*k+1)+1 by omega,List.getElem?_cons_succ]
    · intro k
      rw [odds,e k,show 2*k+1=(2*k)+1 by omega,List.getElem?_cons_succ]
    · simp only [evens,List.length_cons]; omega
    · simp only [odds,List.length_cons]; omega

theorem get_ofListF : ∀ f (l : List Box), l.length≤f → ∀ i, (Tree.ofListF f l).get i=getBox l i
  | 0,l,h,i => by
    have : l=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [Tree.ofListF,Tree.get,getBox]
  | f+1,[],_,i => by simp [Tree.ofListF,Tree.get,getBox]
  | f+1,x::xs,h,i => by
    obtain ⟨e,o,le,lo⟩ := split_get xs
    simp only [List.length_cons] at h
    cases i with
    | zero => simp [Tree.ofListF,Tree.get,getBox]
    | succ i =>
      simp only [Tree.ofListF,Tree.get]
      split
      · next he =>
        rw [get_ofListF f _ (by omega),getBox,getBox,e,List.getElem?_cons_succ,
          show 2*(i/2)=i by omega]
      · next ho =>
        rw [get_ofListF f _ (by omega),getBox,getBox,o,List.getElem?_cons_succ,
          show 2*(i/2)+1=i by omega]

theorem fastBox_eq (bs : List Box) : fastBox bs=atomBox bs := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact get_ofListF _ _ le_rfl i

end ArtGallery.Orthogonal.BoundaryPoint.BoxTree
end
