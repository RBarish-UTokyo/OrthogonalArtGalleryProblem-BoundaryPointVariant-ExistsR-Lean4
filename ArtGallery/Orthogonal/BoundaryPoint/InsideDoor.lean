module

public import ArtGallery.Orthogonal.BoundaryPoint.DoorSubdivision
public import ArtGallery.Existence.Rotate
public import Mathlib.Data.List.Rotate

/-! # A wing attached through a proper subedge of its hub
The returned vertex list follows the old hub to the new door, follows the
complementary wing path, and returns to the hub. Both pieces' straight-line
visibility is preserved for their own points. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.InsideDoor
open Set Geometry Existence WindowGlue

theorem rotate_list (l : List Point) (s : Nat) : (Polygon.mk l).rotate s=⟨l.rotate s⟩ := by
  unfold Polygon.rotate
  congr 1
  apply List.ext_getElem
  · simp [Polygon.n]
  · intro i hi hj
    have npos : 0<l.length := by simpa only [List.length_rotate] using Nat.zero_lt_of_lt hj
    have v : (s+i)%l.length<l.length := Nat.mod_lt _ npos
    simp only [List.getElem_map,List.getElem_range,Polygon.n,Polygon.vtx,List.getElem_rotate]
    simp only [Nat.add_comm s i]
    exact List.getD_eq_getElem (l:=l) (d:=(0,0)) (Nat.mod_lt _ npos)

theorem swap (l r : List Point) : (Polygon.mk (l++r)).rotate l.length=⟨r++l⟩ := by
  rw [rotate_list,List.rotate_append_length_eq]

def output (a b : Point) (u : List Point) (x y : Point) (v : List Point) : Polygon :=
  ⟨((a::u)++(b::x::v))++[y]⟩

theorem glued {a b z : Point} {u v : List Point} {t₁ t₂ : ℝ}
    (h₁ : 0<t₁) (h₂ : t₁<t₂) (h₃ : t₂<1) (hubSimple : (first a b u).Simple)
    (wingSimple : (first (lerp b a t₁) (lerp b a t₂) (v++[z])).Simple)
    (contact : (first a b u).filled∩(first (lerp b a t₁) (lerp b a t₂) (v++[z])).filled =
      ArtGallery.segment (lerp b a t₁) (lerp b a t₂)) :
    let x := lerp b a t₁
    let y := lerp b a t₂
    let H := first a b u
    let W := first x y (v++[z])
    let P := output a b u x y (v++[z])
    P.Simple ∧ P.filled=H.filled∪W.filled ∧
      WindowTree.Attachments H.filled P.filled ∧ WindowTree.Attachments W.filled P.filled := by
  let x := lerp b a t₁; let y := lerp b a t₂
  let H := first a b u; let W := first x y (v++[z])
  let R := whole a b u [x,y]
  let H' := first y x ((a::u)++[b])
  let F := whole y x ((a::u)++[b]) (v++[z])
  let P := output a b u x y (v++[z])
  let pre := (a::u)++[b,x]
  let body := (a::u)++(b::x::(v++[z]))
  obtain ⟨refined,_,same⟩ := DoorSubdivision.insert hubSimple h₁ h₂ h₃
  change R.Simple at refined
  change R.filled=H.filled at same
  have rep : R=(⟨pre++[y]⟩:Polygon) := by simp [R,pre,whole,List.append_assoc]
  have oriented : R.rotate pre.length=H' := by
    rw [rep,swap]; simp [H',first,pre,List.append_assoc]
  have Hsimple : H'.Simple := oriented ▸ simple_rotate R pre.length refined
  have hf : H'.filled=H.filled := by rw [← oriented,filled_rotate,same]
  have meet : H'.filled∩W.filled=ArtGallery.segment y x := by rw [hf,segment_comm y x]; exact contact
  obtain ⟨fSimple,filled,fromHub,fromWing⟩ := WindowGlue.joined Hsimple wingSimple meet
  change F.Simple at fSimple
  change F.filled=H'.filled∪W.filled at filled
  change WindowTree.Attachments H'.filled F.filled at fromHub
  change WindowTree.Attachments W.filled F.filled at fromWing
  have front : F=(⟨[y]++body⟩:Polygon) := by simp [F,whole,body,List.append_assoc]
  have returnToHub : F.rotate 1=P := by
    rw [front]
    exact swap [y] body
  have pf : P.filled=F.filled := by rw [← returnToHub,filled_rotate]
  change P.Simple ∧ P.filled=H.filled∪W.filled ∧
    WindowTree.Attachments H.filled P.filled ∧ WindowTree.Attachments W.filled P.filled
  refine ⟨?_,?_,?_,?_⟩
  · rw [← returnToHub]; exact simple_rotate F 1 fSimple
  · rw [pf,filled,hf]
  · rw [pf,← hf]; exact fromHub
  · rw [pf]; exact fromWing

end ArtGallery.Orthogonal.BoundaryPoint.InsideDoor
end
