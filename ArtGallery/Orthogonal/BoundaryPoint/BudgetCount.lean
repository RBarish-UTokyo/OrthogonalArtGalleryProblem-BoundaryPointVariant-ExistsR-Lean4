module

public import ArtGallery.Orthogonal.BoundaryPoint.OwnerAssembly

/-! # The emitted guard budget counts the hub and private roles

`ChartDrawing.vertices` emits the budget `#slots + Σ_rows (corridor roles + room roles + 1)`.
The private roles of a row are its role records, one per corridor and room role,
and the hub roles are one per slot and one per row. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.BudgetCount
open ChartDrawing CatalogPlan CompiledSize HubOwners RectContour

theorem records_length (t : Template) (n j : Nat) (rs : List Nat) :
    (GlobalPins.records t n j rs).length+1=(drawOne t n j rs).2 := by
  simp [GlobalPins.records,drawOne,CorridorProgram.Layout.coords,PlanGeometry.ArithmeticRoom.coords]

theorem choose_length {ts : List Template} {n j tag : Nat} {rs : List Nat} (h : tag<ts.length) :
    (choose ts (fun t => GlobalPins.records t n j rs) tag []).length+1=
      (choose ts (fun t => drawOne t n j rs) tag (none,0)).2 := by
  induction ts generalizing tag with
  | nil => simp at h
  | cons t ts ih =>
    cases tag with
    | zero => exact records_length t n j rs
    | succ k => simpa [choose] using ih (by simpa using h)

theorem zipIdx_ofFn {α : Type} (l : List α) :
    l.zipIdx=List.ofFn fun i : Fin l.length => (l[i],(i:Nat)) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂; simp [List.getElem_zipIdx]

theorem card_eq {eqs : List ETRINV.Constraint} (ne : eqs≠[]) {v : List Vertex} {g : Nat}
    (out : CandidateWord.vertices eqs=some (v,g)) :
    Fintype.card (HubRole eqs)+Fintype.card (PrivateRoles.Role eqs)=g := by
  have nonempty : (compile eqs).1.isEmpty=false := by
    have := HubRoles.rows_pos ne
    exact List.isEmpty_eq_false_iff.mpr (List.length_pos_iff.mp this)
  change ChartDrawing.vertices (compile eqs)=some (v,g) at out
  unfold ChartDrawing.vertices at out
  simp only [nonempty,Bool.false_eq_true,ite_false] at out
  split at out
  · obtain ⟨l,_,eq⟩ := Option.map_eq_some_iff.mp out
    have hg := (congrArg Prod.snd eq).symm
    simp only at hg
    rw [hg]
    have rowsN : Fintype.card (HubRole eqs)=(PlacedSlots.starts eqs).length+(compile eqs).1.length := by
      simp [HubRole,slots]
    have slotsN : (PlacedSlots.starts eqs).length=(compile eqs).2.length := by simp [PlacedSlots.starts]
    have priv : Fintype.card (PrivateRoles.Role eqs)=∑ i : Fin (compile eqs).1.length, (PrivateRoles.records eqs i).length := by
      simp [PrivateRoles.Role,Fintype.card_sigma]
    have sumEq : ((batch (max (compile eqs).1.length (compile eqs).2.length) (compile eqs).1).map Prod.snd).sum=
        ∑ i : Fin (compile eqs).1.length, ((PrivateRoles.records eqs i).length+1) := by
      unfold batch
      rw [zipIdx_ofFn,List.map_ofFn,List.map_ofFn,List.sum_ofFn]
      apply Finset.sum_congr rfl
      intro i _
      have valid := (CandidateTotal.valid_row (List.getElem_mem i.isLt)).1
      simp only [Function.comp_apply,PrivateRoles.records,GlobalPins.emitted]
      rw [← choose_length (ts:=catalog) (by simpa [catalog] using valid)]
      rfl
    rw [rowsN,slotsN,priv]
    change _=(compile eqs).2.length+((batch (scale eqs) (compile eqs).1).map Prod.snd).sum
    rw [show scale eqs=max (compile eqs).1.length (compile eqs).2.length from rfl,sumEq,Finset.sum_add_distrib]
    simp; ring
  · cases out

end ArtGallery.Orthogonal.BoundaryPoint.BudgetCount
end
