module

public import ArtGallery.Orthogonal.BoundaryPoint.HighStep
public import ArtGallery.Orthogonal.BoundaryPoint.HubDoors

/-! # The actual closed seam belongs to the two input polygons -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.DoorSegment
open HighStep Geometry RectContour ContourJoin BoundaryChart BankCoordinates

theorem horizontal {a b x y : ℝ} (order : a<b) (lo : a≤x) (hi : x≤b) :
    (x,y)∈ArtGallery.segment (a,y) (b,y) := by
  refine ⟨(x-a)/(b-a),div_nonneg (sub_nonneg.mpr lo) (sub_nonneg.mpr order.le),
    (div_le_iff₀ (sub_pos.mpr order)).mpr (by linarith),?_⟩
  simp only [sub_self,mul_zero,add_zero,Prod.mk.injEq,and_true,div_mul_cancel₀ _ (sub_ne_zero.mpr order.ne')]
  ring

private theorem vertex {l : List Vertex} (f : Vertex → Point) {j : Nat} (h : j<l.length) :
    (Polygon.mk (l.map f)).vtx j=f (l.getD j (0,0)) := by
  unfold Polygon.vtx
  rw [List.getD_eq_getElem _ _ (by simpa using h),List.getElem_map,List.getD_eq_getElem _ _ h]

theorem zip_edge {l : List Vertex} {a b : Vertex} (h : (a,b)∈l.zip (l.drop 1++l.take 1)) :
    ArtGallery.segment (ratPoint a) (ratPoint b) ⊆ (Polygon.mk (l.map ratPoint)).boundary := by
  have ne : l≠[] := by intro z; subst l; simp at h
  have pos := List.length_pos_iff.mpr ne
  rw [← List.rotate_eq_drop_append_take (by omega : 1≤l.length)] at h
  obtain ⟨i,hi,pair⟩ := List.mem_iff_getElem.mp h
  simp only [List.length_zip,List.length_rotate,min_self] at hi
  simp only [List.getElem_zip,List.getElem_rotate] at pair
  have first := congrArg Prod.fst pair
  have last := congrArg Prod.snd pair
  let P : Polygon := ⟨l.map ratPoint⟩
  have n : P.n=l.length := by simp [P,Polygon.n]
  intro p hp
  refine ⟨i,n ▸ hi,?_⟩
  change p∈ArtGallery.segment (P.vtx i) (P.vtx ((i+1)%P.n))
  rw [n,vertex ratPoint hi,vertex ratPoint (Nat.mod_lt _ pos),
    List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ (Nat.mod_lt _ pos)]
  simp only [Prod.fst,Prod.snd] at first last
  rwa [first,last]

theorem in_hub (n rows j : Nat) (ss : List ℚ) (big : 65≤n) (member : j<rows)
    {p : Point} (inDoor : Mouth (door j) (W n) p) : p∈(Polygon.mk ((hubCycle n rows ss).map ratPoint)).filled := by
  have top : HubDoors.topEdge j∈(List.range rows).map HubDoors.topEdge :=
    List.mem_map.mpr ⟨j,List.mem_range.mpr member,rfl⟩
  rw [← HubDoors.ceiling n rows ss big] at top
  have e := List.mem_of_mem_filter top
  apply Jordan.boundary_subset_filled _
  apply zip_edge (l:=hubCycle n rows ss) (a:=(HubDoors.topEdge j).1) (b:=(HubDoors.topEdge j).2) e
  obtain ⟨x,y⟩ := p
  obtain ⟨h1,L,R⟩ := inDoor
  change y=1 at h1
  subst y
  rw [segment_comm]
  simp only [HubDoors.topEdge,ratPoint,Rat.cast_sub,Rat.cast_add,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one]
  have small : (W n:ℝ)≤1/2 := by
    rw [cast_W]
    exact BankPitch.width_le_half (by exact_mod_cast (show 1≤n by omega))
  apply horizontal <;> linarith

theorem in_wing {l path : List Vertex} {d w : ℚ} (hw : 0<w) (out : atDoor d w l=some path)
    {p : Point} (belongs : Mouth d w p) : p∈(Polygon.mk (path.map ratPoint)).filled := by
  let i := l.idxOf (0,1)
  unfold atDoor at out
  dsimp only at out
  split at out
  · contradiction
  next good =>
    have H : ¬((decide (i ≥ l.length) || (l.getD ((i+1) % l.length) (0,0) != (w,1)))=true) := good
    have hi : i<l.length := by by_contra! k; simp [k] at H
    have successor : l.getD ((i+1)%l.length) (0,0)=(w,1) := by
      simpa only [Nat.not_le.mpr hi,decide_false,Bool.false_or,bne_iff_ne,not_not] using H
    have first : l.getD i (0,0)=(0,1) := (List.getD_eq_getElem _ _ hi).trans (List.getElem_idxOf hi)
    obtain rfl := Option.some.inj out
    change p∈(Polygon.mk (((l.drop (i+1)++l.take (i+1)).map _).map ratPoint)).filled
    rw [←List.rotate_eq_drop_append_take (by omega : i+1≤l.length),List.map_map]
    change p∈(Polygon.mk ((l.rotate (i+1)).map (moved d))).filled
    rw [List.map_rotate,←InsideDoor.rotate_list,Existence.filled_rotate]
    apply Jordan.boundary_subset_filled _
    let P : Polygon := ⟨l.map (moved d)⟩
    have n : P.n=l.length := by simp [P,Polygon.n]
    refine ⟨i,n ▸ hi,?_⟩
    change p∈ArtGallery.segment (P.vtx i) (P.vtx ((i+1)%P.n))
    rw [n,vertex (moved d) hi,vertex (moved d) (Nat.mod_lt _ (by omega)),first,successor]
    obtain ⟨x,y⟩ := p
    obtain ⟨one,L,R⟩ := belongs
    change y=1 at one
    subst y
    simp only [moved,ratPoint,zero_add,Rat.cast_add,Rat.cast_one]
    apply horizontal
    · linarith [(Rat.cast_pos (K:=ℝ)).mpr hw]
    · exact L
    · simpa [add_comm] using R

end ArtGallery.Orthogonal.BoundaryPoint.DoorSegment
end
