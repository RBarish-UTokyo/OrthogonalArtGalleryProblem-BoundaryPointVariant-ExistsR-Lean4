module

public import ArtGallery.Orthogonal.BoundaryPoint.WindowSplice
public import ArtGallery.Jordan.Local

/-! # Cutting the closing edge from a simple polygon -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SimplePaths
open Set Geometry ArtGallery.Stade.Chain

theorem trace_edge {z : Point} (l : List Point) (hz : z∈chainSet l) :
    ∃ i, i+1<l.length ∧ z∈edgeSeg l i := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
    cases l with
    | nil => contradiction
    | cons b l =>
      rcases hz with h|h
      · exact ⟨0,by simp,edgeSeg_cons_cons_zero .. ▸ h⟩
      · obtain ⟨i,hi,hp⟩ := ih h
        exact ⟨i+1,Nat.succ_lt_succ hi,(edgeSeg_cons_succ a (b::l) i).symm ▸ hp⟩

private theorem from_edges (l : List Point)
    (distinct : ∀ i, i+1<l.length → l.getD i (0,0)≠l.getD (i+1) (0,0))
    (apart : ∀ i j, i<j → j+1<l.length → edgeSeg l i∩edgeSeg l j ⊆ {l.getD (i+1) (0,0)}) :
    ChainSimple l := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    cases l with
    | nil => trivial
    | cons b l =>
      refine ⟨distinct 0 (by simp),?_,ih ?_ ?_⟩
      · rintro z ⟨atA,atB⟩
        obtain ⟨j,hj,hit⟩ := trace_edge (b::l) atB
        apply apart 0 (j+1) (Nat.zero_lt_succ _) (Nat.succ_lt_succ hj)
        exact ⟨edgeSeg_cons_cons_zero .. ▸ atA,(edgeSeg_cons_succ a (b::l) j).symm ▸ hit⟩
      · intro i hi
        exact distinct (i+1) (Nat.succ_lt_succ hi)
      · intro i j h hi
        simpa only [edgeSeg_cons_succ,List.getD_cons_succ] using
          apart (i+1) (j+1) (Nat.succ_lt_succ h) (Nat.succ_lt_succ hi)

private theorem old_edge (l : List Point) {i : Nat} (h : i+1<l.length) :
    (Polygon.mk l).edge i=edgeSeg l i := by
  simp only [Polygon.edge,Polygon.n,edgeSeg,Polygon.vtx,Nat.mod_eq_of_lt h]

theorem open_simple {l : List Point} (h : (Polygon.mk l).Simple) : ChainSimple l := by
  let P : Polygon := ⟨l⟩
  apply from_edges l
  · intro i hi
    exact Jordan.simple_vtx_ne (P:=P) h (i:=i) (j:=i+1) (by change i<l.length; omega) hi (by omega)
  · intro i j ij hj z hz
    have hi : i+1<l.length := by omega
    rw [← old_edge l hi,← old_edge l hj] at hz
    obtain ⟨h1,h2⟩ := h.2.2 i j (by change i<l.length; omega) (by change j<l.length; omega) ij.ne ▸ hz
    simp only [Polygon.n,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] at h1 h2
    rcases h1 with e|e
    · rcases h2 with f|f
      · exact (ij.ne (h.2.1 i j (by change i<l.length; omega) (by change j<l.length; omega) (e.symm.trans f))).elim
      · exact (show i≠j+1 by omega) (h.2.1 i (j+1) (by change i<l.length; omega) hj (e.symm.trans f)) |>.elim
    · exact e

theorem trace_in {l : List Point} : chainSet l ⊆ (Polygon.mk l).filled := by
  intro z h
  obtain ⟨i,hi,he⟩ := trace_edge l h
  exact Or.inl ⟨i,by change i<l.length; omega,old_edge l hi ▸ he⟩

theorem closing {a b : Point} {u : List Point} (h : (Polygon.mk ((a::u)++[b])).Simple) :
    ArtGallery.segment a b ∩ chainSet ((a::u)++[b]) ⊆ {a,b} := by
  let l := (a::u)++[b]
  let P : Polygon := ⟨l⟩
  let last := (a::u).length
  have n : P.n=last+1 := by simp [l,P,last,Polygon.n]
  have first : P.vtx 0=a := rfl
  have final : P.vtx last=b := getD_append_singleton_last _ _
  have next : (last+1)%P.n=0 := by rw [n,Nat.mod_self]
  have edge : P.edge last=ArtGallery.segment a b := by rw [Polygon.edge,final,next,first,segment_comm]
  rintro z ⟨hDoor,hChain⟩
  obtain ⟨i,hi,hm⟩ := trace_edge l hChain
  have len : i+1<P.n := hi
  have pair : z∈P.edge last∩P.edge i := ⟨edge ▸ hDoor,old_edge l hi ▸ hm⟩
  have hs : P.Simple := h
  rw [hs.2.2 last i (by omega) (by omega) (by omega)] at pair
  have endpoints := pair.1
  change z=P.vtx last ∨ z=P.vtx ((last+1)%P.n) at endpoints
  rw [final,next,first] at endpoints
  exact endpoints.symm

theorem door_in {a b : Point} (u : List Point) :
    ArtGallery.segment a b ⊆ (Polygon.mk ((a::u)++[b])).boundary := by
  let P : Polygon := ⟨(a::u)++[b]⟩
  let last := (a::u).length
  have n : P.n=last+1 := by simp [P,last,Polygon.n]
  have x : P.vtx last=b := getD_append_singleton_last _ _
  have f : P.vtx 0=a := rfl
  intro p hp
  refine ⟨last,by change last<P.n; omega,?_⟩
  change p∈P.edge last
  rw [Polygon.edge,n,Nat.mod_self,x,f,segment_comm]
  exact hp

end ArtGallery.Orthogonal.BoundaryPoint.SimplePaths
end
