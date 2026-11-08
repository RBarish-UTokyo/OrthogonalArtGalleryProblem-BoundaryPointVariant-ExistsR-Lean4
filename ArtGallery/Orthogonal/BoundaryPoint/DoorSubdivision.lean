module

public import ArtGallery.Orthogonal.BoundaryPoint.WindowGlue

/-! # Cutting a door strictly inside a long edge
Inserting its two ordered endpoints into the vertex list preserves simplicity,
boundary and filled set. This permits door gluing on a proper hub subedge. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.DoorSubdivision
open Set Geometry ArtGallery.Stade.Chain WindowGlue

theorem boundary_path (a b : Point) (u : List Point) :
    (first a b u).boundary=chainSet ((a::u)++[b])∪ArtGallery.segment a b := by
  let Q := first a b u; let xs := (a::u)++[b]; let k := (a::u).length
  have n : Q.n=k+1 := by simp [Q,first,k,Polygon.n]
  have bV : Q.vtx k=b := getD_append_singleton_last _ _
  have aV : Q.vtx 0=a := rfl
  have endEdge : Q.edge k=ArtGallery.segment a b := by
    rw [Polygon.edge,bV,n,Nat.mod_self,aV,segment_comm]
  have openEdge (i) (hi : i+1<Q.n) : Q.edge i=edgeSeg xs i := by
    simp only [Polygon.edge,Nat.mod_eq_of_lt hi]
    rfl
  ext z
  constructor
  · rintro ⟨i,hi,h⟩
    change i<Q.n at hi
    change z∈Q.edge i at h
    by_cases last : i=k
    · exact Or.inr (endEdge ▸ last ▸ h)
    · have short : i+1<Q.n := by omega
      exact Or.inl (edgeSeg_subset short (openEdge i short ▸ h))
  · rintro (h|h)
    · obtain ⟨i,hi,edge⟩ := SimplePaths.trace_edge xs h
      have bound : i+1<Q.n := hi
      exact ⟨i,by change i<Q.n; omega,openEdge i bound ▸ edge⟩
    · exact SimplePaths.door_in _ h

private theorem mix (a b : Point) (u v t : ℝ) :
    lerp (lerp a b u) (lerp a b v) t=lerp a b (u+t*(v-u)) := by
  ext <;> simp only [lerp] <;> ring

theorem subsegment (a b : Point) {u v : ℝ} (h : u<v) :
    ArtGallery.segment (lerp a b u) (lerp a b v)=lerp a b '' Icc u v := by
  ext z
  constructor
  · intro hz
    obtain ⟨t,ht,hu,rfl⟩ := mem_segment_iff_lerp.mp hz
    exact ⟨_,⟨by linarith [mul_nonneg ht (sub_nonneg.mpr h.le)],
      by linarith [mul_le_mul_of_nonneg_right hu (sub_nonneg.mpr h.le)]⟩,(mix a b u v t).symm⟩
  · rintro ⟨w,hw,rfl⟩
    let t := (w-u)/(v-u)
    have t0 : 0≤t := div_nonneg (sub_nonneg.mpr hw.1) (sub_nonneg.mpr h.le)
    have t1 : t≤1 := (div_le_one (sub_pos.mpr h)).mpr (sub_le_sub_right hw.2 _)
    have eq : u+t*(v-u)=w := by dsimp [t]; rw [div_mul_cancel₀ _ (sub_ne_zero.mpr h.ne')]; ring
    exact mem_segment_iff_lerp.mpr ⟨t,t0,t1,by rw [mix,eq]⟩

private theorem straight {a b : Point} (ne : a≠b) {u v : ℝ} (u0 : 0<u) (uv : u<v) (v1 : v<1) :
    let f := lerp a b
    ChainSimple [a,f u,f v,b] ∧ chainSet [a,f u,f v,b]=ArtGallery.segment a b := by
  let f := lerp a b
  have h0 : a=f 0 := (lerp_zero ..).symm
  have h1 : b=f 1 := (lerp_one ..).symm
  have inject : Function.Injective f := lerp_injective ne
  have e0 : ArtGallery.segment (f 0) (f u)=f '' Icc 0 u := subsegment a b u0
  have e1 : ArtGallery.segment (f u) (f v)=f '' Icc u v := subsegment a b uv
  have e2 : ArtGallery.segment (f v) (f 1)=f '' Icc v 1 := subsegment a b v1
  have e : ArtGallery.segment (f 0) (f 1)=f '' Icc 0 1 := subsegment a b (show (0:ℝ)<1 by norm_num)
  have paths : ChainSimple [f 0,f u,f v,f 1] := by
    refine ⟨fun eq => u0.ne (inject eq),?_,fun eq => uv.ne (inject eq),?_,fun eq => v1.ne (inject eq),by simp,by simp⟩
    · rintro z ⟨zl,zr⟩
      rw [e0] at zl
      obtain ⟨t,ht,rfl⟩ := zl
      simp only [chainSet_cons_cons,chainSet_single,Set.union_empty,e1,e2] at zr
      rcases zr with ⟨w,hw,eq⟩|⟨w,hw,eq⟩
      · have eq' := inject eq
        have hh : t=u := by linarith [ht.2,hw.1]
        exact congrArg f hh
      · have eq' := inject eq; exact (by linarith [ht.2,hw.1] : False).elim
    · rintro z ⟨zl,zr⟩
      rw [e1] at zl
      obtain ⟨t,ht,rfl⟩ := zl
      simp only [chainSet_cons_cons,chainSet_single,Set.union_empty,e2] at zr
      obtain ⟨w,hw,eq⟩ := zr
      have eq' := inject eq
      have hh : t=v := by linarith [ht.2,hw.1]
      exact congrArg f hh
  have trace : chainSet [f 0,f u,f v,f 1]=ArtGallery.segment (f 0) (f 1) := by
    simp only [chainSet_cons_cons,chainSet_single,Set.union_empty,e0,e1,e2,e]
    rw [← Set.image_union,← Set.image_union]
    congr 1
    ext w
    simp only [Set.mem_union,Set.mem_Icc]
    constructor
    · rintro (h|(h|h)) <;> constructor <;> linarith [h.1,h.2]
    · intro h
      rcases le_total w u with hu|hu
      · exact Or.inl ⟨h.1,hu⟩
      rcases le_total w v with hv|hv
      · exact Or.inr (Or.inl ⟨hu,hv⟩)
      · exact Or.inr (Or.inr ⟨hv,h.2⟩)
  exact ⟨by simpa only [f,lerp_zero,lerp_one] using paths,by simpa only [f,lerp_zero,lerp_one] using trace⟩

theorem insert {a b : Point} {u : List Point} (h : (first a b u).Simple)
    {t₁ t₂ : ℝ} (h₁ : 0<t₁) (h₂ : t₁<t₂) (h₃ : t₂<1) :
    let x := lerp b a t₁
    let y := lerp b a t₂
    let R := whole a b u [x,y]
    R.Simple ∧ R.boundary=(first a b u).boundary ∧ R.filled=(first a b u).filled := by
  let x := lerp b a t₁; let y := lerp b a t₂
  let R := whole a b u [x,y]
  have A := SimplePaths.open_simple h
  have nodup : (a::(u++[b])).Nodup := A.nodup
  have ne : b≠a := by intro eq; exact (List.nodup_cons.mp nodup).1 (by simp [eq])
  have ⟨B,tr⟩ := straight ne h₁ h₂ h₃
  change chainSet [b,x,y,a]=ArtGallery.segment b a at tr
  rw [segment_comm b a] at tr
  have touch : chainSet ((a::u)++[b])∩chainSet [b,x,y,a] ⊆ {a,b} := by
    rw [tr,Set.inter_comm]; exact SimplePaths.closing h
  have simple : R.Simple := by
    simpa only [R,whole,List.cons_append,List.append_assoc,List.singleton_append,List.nil_append] using
      WindowSplice.simple (a:=a) (b:=b) (z:=y) (u:=u) (v:=[x]) A B touch
  have equal : R.boundary=(first a b u).boundary := by
    have arrange : R=first a y (u++[b,x]) := by simp [R,whole,first,List.append_assoc]
    rw [arrange,boundary_path,boundary_path]
    have cut : chainSet ((a::(u++[b,x]))++[y])=
        chainSet ((a::u)++[b])∪chainSet [b,x,y] := by
      simpa only [List.cons_append,List.singleton_append,List.append_assoc,List.nil_append] using
        chainSet_append_cons (a::u) b [x,y]
    rw [cut,Set.union_assoc,← tr]
    congr 1
    simp [segment_comm a y,Set.union_assoc]
  exact ⟨simple,equal,by change R.filled=(first a b u).filled; unfold Polygon.filled; rw [equal]⟩

end ArtGallery.Orthogonal.BoundaryPoint.DoorSubdivision
end
