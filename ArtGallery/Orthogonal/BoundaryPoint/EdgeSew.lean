module

public import ArtGallery.Orthogonal.BoundaryPoint.InsideDoor

/-! # Repeated proper-subedge joins along a cyclic vertex sequence
Rows keep the original endpoints even after earlier doors have been spliced
in. Each subsequent disjoint wing retains its exact seam with the partial
gallery. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.EdgeSew
open Set Geometry Existence WindowGlue WindowTree

structure Row where
  start : Point
  stop : Point
  path : List Point

def wing (r : Row) : Polygon := ⟨r.path⟩
def part (r : Row) : Set Point := if r.path=[] then ∅ else (wing r).filled
def added : List Row → Set Point
  | [] => ∅
  | r::rs => part r ∪ added rs

def before (pre : List Point) (rs : List Row) : Polygon := ⟨pre++rs.map Row.start⟩
def after (pre : List Point) (rs : List Row) : Polygon := ⟨pre++rs.flatMap (fun r => r.start::r.path)⟩

def successive : List Row → Prop
  | [] => True
  | [r] => r.path=[]
  | r::s::rs => r.stop=s.start ∧ successive (s::rs)

def Shape (H : Set Point) (r : Row) : Prop := r.path≠[] →
  ∃ (t₁ t₂ : ℝ) (v : List Point) (z : Point),
    let x := lerp r.start r.stop t₁
    let y := lerp r.start r.stop t₂
    0<t₁ ∧ t₁<t₂ ∧ t₂<1 ∧ r.path=(x::v)++[z,y] ∧
    (wing r).Simple ∧ H∩(wing r).filled=ArtGallery.segment x y

private theorem spin_fill (l r : List Point) :
    (Polygon.mk (l++r)).filled=(Polygon.mk (r++l)).filled := by
  rw [←InsideDoor.swap,filled_rotate]

private theorem spin_simple (l r : List Point) :
    (Polygon.mk (l++r)).Simple ↔ (Polygon.mk (r++l)).Simple := by
  constructor
  · intro h; rw [←InsideDoor.swap]; exact simple_rotate _ _ h
  · intro h; rw [←InsideDoor.swap]; exact simple_rotate _ _ h

private theorem sew (pre post : List Point) (r : Row)
    (ne : r.path≠[]) (H : (Polygon.mk (pre++r.start::r.stop::post)).Simple)
    (S : Shape (Polygon.mk (pre++r.start::r.stop::post)).filled r) :
    let old : Polygon := ⟨pre++r.start::r.stop::post⟩
    let next : Polygon := ⟨pre++r.start::(r.path++r.stop::post)⟩
    next.Simple ∧ next.filled=old.filled∪(wing r).filled ∧
      Attachments old.filled next.filled ∧ Attachments (wing r).filled next.filled := by
  obtain ⟨t,u,v,z,h₁,h₂,h₃,path,W,contact⟩ := S ne
  let x := lerp r.start r.stop t
  let y := lerp r.start r.stop u
  let keep := post++pre
  let old : Polygon := ⟨pre++r.start::r.stop::post⟩
  let next : Polygon := ⟨pre++r.start::(r.path++r.stop::post)⟩
  have Hsimple : (first r.stop r.start keep).Simple := by
    have h := (spin_simple (pre++[r.start]) (r.stop::post)).mp (by simpa [List.append_assoc] using H)
    simpa [first,keep,List.append_assoc] using h
  have same : (first r.stop r.start keep).filled=old.filled := by
    simpa [first,keep,old,List.append_assoc] using (spin_fill (pre++[r.start]) (r.stop::post)).symm
  have sameWing : first x y (v++[z])=wing r := by simp [first,wing,path,x,y,List.append_assoc]
  have glued := InsideDoor.glued (a:=r.stop) (b:=r.start) (u:=keep) (v:=v) (z:=z)
    h₁ h₂ h₃ Hsimple (sameWing ▸ W) (by rw [same,sameWing]; exact contact)
  let G := InsideDoor.output r.stop r.start keep x y (v++[z])
  change G.Simple ∧ G.filled=(first r.stop r.start keep).filled∪(first x y (v++[z])).filled ∧
    Attachments (first r.stop r.start keep).filled G.filled ∧ Attachments (first x y (v++[z])).filled G.filled at glued
  rw [same,sameWing] at glued
  let l := pre++r.start::r.path
  let s := r.stop::post
  have original : next=(⟨l++s⟩:Polygon) := by simp [next,l,s,List.append_assoc]
  have rotated : G=(⟨s++l⟩:Polygon) := by simp [G,InsideDoor.output,keep,s,l,path,x,y,List.append_assoc]
  have filled : G.filled=next.filled := by rw [original,rotated,spin_fill]
  change next.Simple ∧ next.filled=old.filled∪(wing r).filled ∧ _
  refine ⟨?_,filled ▸ glued.2.1,filled ▸ glued.2.2⟩
  rw [original]
  exact (spin_simple l s).mpr (rotated ▸ glued.1)

structure Joined (pre : List Point) (rs : List Row) : Prop where
  simple : (after pre rs).Simple
  filled : (after pre rs).filled=(before pre rs).filled∪added rs
  base : Attachments (before pre rs).filled (after pre rs).filled
  leaves : ∀ r∈rs, r.path≠[] → Attachments (wing r).filled (after pre rs).filled

theorem extend {a b c : Set Point} (u : Attachments a b) (v : Attachments b c) : Attachments a c := by
  induction v with
  | start => exact u
  | attach _ closed cut ih => exact ih.attach closed cut

private theorem one_row (pre : List Point) (r : Row) (rs : List Row) (order : successive (r::rs))
    (H : (before pre (r::rs)).Simple) (ok : Shape (before pre (r::rs)).filled r) :
    let P := before pre (r::rs)
    let Q := before (pre++r.start::r.path) rs
    Q.Simple ∧ Q.filled=P.filled∪part r ∧ Attachments P.filled Q.filled ∧
      (r.path≠[] → Attachments (wing r).filled Q.filled) := by
  by_cases empty : r.path=[]
  · have same : before (pre++r.start::r.path) rs=before pre (r::rs) := by simp [before,empty,List.append_assoc]
    dsimp only
    rw [same]
    exact ⟨H,by simp [part,empty],Attachments.start (Jordan.isClosed_filled _),fun ne => (ne empty).elim⟩
  · cases rs with
    | nil => exact (empty order).elim
    | cons s rs =>
      have eq := order.1
      have res := sew pre (rs.map Row.start) r empty (by simpa [before,eq] using H) (by simpa [before,eq] using ok)
      simp only [before,List.map_cons,part,empty,ite_false,List.append_assoc,List.cons_append,eq] at res ⊢
      exact ⟨res.1,res.2.1,res.2.2.1,fun _ => res.2.2.2⟩

private theorem preserve {H W : Set Point} {r : Row} (valid : Shape H r) (apart : Disjoint W (part r)) :
    Shape (H∪W) r := by
  intro nonempty
  obtain ⟨t,u,v,z,ht,htu,hu,path,simple,meet⟩ := valid nonempty
  refine ⟨t,u,v,z,ht,htu,hu,path,simple,?_⟩
  rw [←meet,Set.union_inter_distrib_right]
  have disjoint : Disjoint W (wing r).filled := by simpa only [part,nonempty,ite_false] using apart
  rw [Set.disjoint_iff_inter_eq_empty.mp disjoint,Set.union_empty]

theorem assemble (rs : List Row) (pre : List Point) (H : (before pre rs).Simple) (order : successive rs)
    (ok : ∀ r∈rs,Shape (before pre rs).filled r) (apart : rs.Pairwise (fun a b => Disjoint (part a) (part b))) :
    Joined pre rs := by
  induction rs generalizing pre with
  | nil =>
    refine ⟨H,?_,Attachments.start (Jordan.isClosed_filled _),by simp⟩
    simp [before,after,added]
  | cons r rs ih =>
    let head := pre++r.start::r.path
    let P := before pre (r::rs)
    let Q := before head rs
    obtain ⟨s,fill,tree,fromWing⟩ := one_row pre r rs order H (ok r List.mem_cons_self)
    change Q.filled=P.filled∪part r at fill
    have later : ∀ v∈rs,Shape Q.filled v := by
      intro v hv
      rw [fill]
      exact preserve (ok v (List.mem_cons_of_mem _ hv)) ((List.pairwise_cons.mp apart).1 v hv)
    have right : successive rs := by cases rs with | nil => trivial | cons => exact order.2
    have joined := ih head s right later apart.of_cons
    have same : after pre (r::rs)=after head rs := by simp [after,head,List.append_assoc]
    refine ⟨same ▸ joined.simple,?_,same ▸ extend tree joined.base,?_⟩
    · rw [same,joined.filled,show (before head rs).filled=Q.filled by rfl,fill]
      exact Set.union_assoc ..
    · intro v hv ne
      rw [same]
      rcases List.mem_cons.mp hv with eq|hs
      · subst v; exact extend (fromWing ne) joined.base
      · exact joined.leaves v hs ne

end ArtGallery.Orthogonal.BoundaryPoint.EdgeSew
end
