module

public import ArtGallery.Stade.Chains
public import ArtGallery.Orthogonal.BoundaryPoint.WindowTree

/-! # Simplicity after gluing two complementary boundary paths along one door
Each path runs between the two door endpoints. When the complementary paths
meet only at those endpoints, dropping the common door segment produces the
simple boundary cycle of the attached region. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WindowSplice
open Set Geometry ArtGallery.Stade.Chain

theorem reverse_trace (l : List Point) : chainSet l.reverse=chainSet l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b t =>
      have step : (a::b::t).reverse=t.reverse++b::[a] := by simp [List.append_assoc]
      rw [step,chainSet_append_cons]
      have pre : chainSet (t.reverse++[b])=chainSet (b::t) := by simpa only [List.reverse_cons] using ih
      simp [pre,segment_comm b a,Set.union_comm]

theorem reverse_simple (l : List Point) (h : ChainSimple l) : ChainSimple l.reverse := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b t =>
      have pre : ChainSimple (t.reverse++[b]) := by simpa using ih h.tail
      have revTrace : chainSet (t.reverse++[b])=chainSet (b::t) := by simpa using reverse_trace (b::t)
      have endPath : ChainSimple [b,a] := ⟨h.1.symm,by simp,by simp⟩
      have meet : chainSet (t.reverse++[b])∩chainSet [b,a]⊆{b} := by
        rw [revTrace]; simp only [chainSet_cons_cons,chainSet_single,Set.union_empty,segment_comm b a]
        exact fun _ p => h.2.1 ⟨p.2,p.1⟩
      have done := pre.join endPath meet
      simpa [List.reverse_cons,List.append_assoc] using done

theorem simple {a b z : Point} {u v : List Point}
    (A : ChainSimple ((a::u)++[b])) (B : ChainSimple ((b::v)++[z,a]))
    (touch : chainSet ((a::u)++[b]) ∩ chainSet ((b::v)++[z,a]) ⊆ {a,b}) :
    (Polygon.mk (a::(u++b::v)++[z])).Simple := by
  let R := (b::v)++[z]
  have rev : ChainSimple (a::z::(b::v).reverse) := by
    simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append,
      List.cons_append] using reverse_simple _ B
  have part : ChainSimple R := by
    have h : ChainSimple R.reverse := by simpa [R] using rev.tail
    simpa using reverse_simple _ h
  have trace : chainSet (z::(b::v).reverse)=chainSet R := by simpa [R] using reverse_trace R
  have notA : a∉chainSet R := trace ▸ rev.head_not_mem
  have cap : ArtGallery.segment z a ∩ chainSet R ⊆ {z} := by
    rw [← trace,segment_comm z a]; exact rev.2.1
  have notZ : b≠z := by
    have nodup : (b::(v++[z])).Nodup := part.nodup
    intro h; exact (List.nodup_cons.mp nodup).1 (by simp [h])
  have base : b∈chainSet R := mem_chainSet_of_mem (by simp [R]) (by simp [R])
  have decomposition : chainSet ((b::v)++[z,a])=chainSet R∪ArtGallery.segment z a := by
    rw [chainSet_append_cons (b::v) z [a]]
    simp [R]
  have cross : chainSet ((a::u)++[b]) ∩ chainSet R ⊆ {b} := by
    rintro w ⟨ha,hr⟩
    rcases touch ⟨ha,decomposition ▸ Or.inl hr⟩ with h|h
    · exact (notA (h ▸ hr)).elim
    · exact h
  have join : ChainSimple ((a::u)++b::(v++[z])) :=
    ChainSimple.join (l₁:=a::u) (l₂:=v++[z]) A part cross
  have poly : ChainSimple (a::(u++b::v)++[z]) := by
    simpa only [R,List.cons_append,List.append_assoc] using join
  apply simple_of_chain (by simp) poly
  rintro w ⟨se,walk⟩
  have step : w∈chainSet ((a::u)++b::(v++[z])) := by
    simpa only [List.cons_append,List.append_assoc] using walk
  rw [chainSet_append_cons] at step
  rcases step with left|right
  · rcases touch ⟨left,decomposition ▸ Or.inr se⟩ with h|h
    · exact Or.inl h
    · have eq : w=b := h
      exact (notZ (cap ⟨eq ▸ se,base⟩)).elim
  · exact Or.inr (cap ⟨se,right⟩)

end ArtGallery.Orthogonal.BoundaryPoint.WindowSplice
end
