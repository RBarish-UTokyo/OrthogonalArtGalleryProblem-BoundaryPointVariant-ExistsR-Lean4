module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomGlobal
public import ArtGallery.Orthogonal.BoundaryPoint.RoomSound.InvRevGe

/-! # The room relation of an InvRevGe inversion row in the emitted gallery

For a boundary guard set within the budget, the owners of the two moving room roles of an InvRevGe
row stand on their room segments at values `x, y` in `[1/2,2]` (parameters `x-1/2`, `y-1/2`)
with `1 ≤ x (5/2 - y)`. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomRow.InvRevGe
open Set ChartDrawing ContourJoin RectContour BankCoordinates CompiledSize PinTransport Hardening.Invariance
open CatalogPlan HubOwners HubRoles CopyGlobal ArtGallery.Orthogonal.Hard RoomWedge MarginCert CorridorProgram
open RoomGlobal RoomFamily.InvRevGe RoomSound.InvRevGe RoomRelation.InvRevGe DerivedAlgebra RoomCoordinates

def win : QBox := hull (gridBox xAxis yAxis window.1) (gridBox xAxis yAxis window.2)
def xmin : ℚ := coordLo xAxis 0
def box1 : QBox := (lower leftEdge,upper axis,lower bottom,upper top)

theorem door1 : sep (0,1/20800,1,1) win box1=true := by decide +kernel
theorem door_left : (1/20800:ℚ)<xmin := by decide +kernel
theorem room_left : cells.all (fun r => decide (r.1≤xAxis.gaps.length ∧ xmin≤coordLo xAxis r.1))=true := by
  decide +kernel
theorem window_index : window.1.1≤xAxis.gaps.length ∧ window.1.2≤yAxis.gaps.length ∧
    window.2.1≤xAxis.gaps.length ∧ window.2.2≤yAxis.gaps.length := by decide +kernel
theorem role_count : roles.length=4 := by decide +kernel

theorem critical_box {n : Nat} (hn : 65≤n) {z : Point} (h : critical (1/(n:ℝ)) z) : box1.Mem z := by
  obtain ⟨hs0,hs1⟩ := size_bounds hn
  obtain ⟨a,b,c,d⟩ := h
  exact ⟨(lower_le _ hs0 hs1).trans a,b.le.trans (le_upper _ hs0 hs1),(lower_le _ hs0 hs1).trans c,
    d.trans (le_upper _ hs0 hs1)⟩

section Main
variable {eqs : List ETRINV.Constraint} {v : List Vertex} {gN : Nat}
variable (ne : eqs≠[]) (out : CandidateWord.vertices eqs=some (v,gN))
include ne out

local notation "PP" => Polygon.mk (v.map ratPoint)

theorem relation (ancs : List (List Nat)) (G : Finset Point) (hcov : (PP).IsGuardSetOnBoundary (G:Set Point))
    (hall : ∀ ρ : HubRole eqs ⊕ PrivateRoles.Role eqs, ∃ p∈G,
      (PP).Sees p (Sum.elim (HubOwners.group eqs PP).mark (PrivateRoles.group eqs ancs).mark ρ) ∧
      p∈Sum.elim (HubOwners.group eqs PP).spot (PrivateRoles.group eqs ancs).spot ρ ∧
      ∀ q∈G, (PP).Sees q (Sum.elim (HubOwners.group eqs PP).mark (PrivateRoles.group eqs ancs).mark ρ) → q=p)
    (hevery : ∀ p∈G, ∃ ρ : HubRole eqs ⊕ PrivateRoles.Role eqs,
      (PP).Sees p (Sum.elim (HubOwners.group eqs PP).mark (PrivateRoles.group eqs ancs).mark ρ) ∧
      p∈Sum.elim (HubOwners.group eqs PP).spot (PrivateRoles.group eqs ancs).spot ρ)
    (i : Fin (PrivateRoles.rows eqs).length) {t : Template}
    (ht : catalog[((PrivateRoles.rows eqs)[i]).1]?=some t)
    (hroom : t.room=⟨xAxis,yAxis,cells,roles⟩)
    (hok : ok (params ((PrivateRoles.rows eqs)[i]).2.length) [] (t.corridor.baseRows++t.corridor.rest)=true)
    (split : let s : ℚ := 1/(scale eqs)
      let args := s::(((i:Nat):ℚ)*s)::(((PrivateRoles.rows eqs)[i]).2.map fun (k:Nat) => (k:ℚ)*s)
      let pt := gridPt (xAxis.coordsR (1/(scale eqs:ℝ))) (yAxis.coordsR (1/(scale eqs:ℝ)))
      (BoundaryChart.actual t.chart (ShapeRefs.join (t.corridor.coords args) (t.room.coords s))).filled=
        WingTiles.cells (t.corridor.coords args).1 ∪ (room (scale eqs)).filled ∧
      WingTiles.cells (t.corridor.coords args).1 ∩ (room (scale eqs)).filled=ArtGallery.segment (pt window.1) (pt window.2))
    (clear1 : corridorClear t.corridor win box1 xmin=true)
    (hc : (PrivateRoles.records eqs i).length=t.corridor.roles.length+4) :
    ∃ x y : ℝ, InRange x ∧ InRange y ∧
      (∀ k : Fin (PrivateRoles.records eqs i).length, ∀ m t', (k:Nat)=t.corridor.roles.length+m →
        (m=0 ∧ t'=x-1/2 ∨ m=1 ∧ t'=y-1/2) →
        ∀ p∈G, (PP).Sees p ((PrivateRoles.group eqs ancs).mark ⟨i,k⟩) →
          shift (-(door (i:Nat))) p=guard (1/(scale eqs:ℝ)) m t') ∧
      1≤x*(5/2-y) := by
  set n := scale eqs with hn_def
  have hn : 65≤n := (scale_bounds ne).1
  set d := door (i:Nat)
  set c := t.corridor.roles.length
  obtain ⟨hs0,hs1⟩ := size_bounds hn
  simp only at split
  -- the frame of the room
  have wi := window_index
  obtain ⟨F,tree⟩ := frame ne out i ht split.1 (tiles_closed _) (Jordan.isClosed_filled _) split.2
    (gridBox_mem xAxis yAxis wi.1 wi.2.1 hs0 hs1) (gridBox_mem xAxis yAxis wi.2.2.1 wi.2.2.2 hs0 hs1)
    (xmin:=xmin) (by rw [RoomFill.InvRevGe.filled_eq n hn]; exact cells_left xAxis yAxis cells xmin room_left hs0 hs1) door_left
  -- the owners of the room roles
  let role (m : Nat) (hm : m<4) : PrivateRoles.Role eqs := ⟨i,⟨c+m,by rw [hc]; omega⟩⟩
  have own (m : Nat) (hm : m<4) := hall (.inr (role m hm))
  let owner (m : Nat) : Point := if hm : m<4 then Classical.choose (own m hm) else 0
  have owner_spec (m : Nat) (hm : m<4) := Classical.choose_spec (own m hm)
  have owner_eq (m : Nat) (hm : m<4) : owner m=Classical.choose (own m hm) := dif_pos hm
  let Gf (m : Nat) : Point := shift (-d) (owner m)
  have hroles : t.room.roles=roles := by rw [hroom]
  -- the pins
  have pins : ∀ m, m<4 → Gf m∈spot (1/(n:ℝ)) m := by
    intro m hm
    have hsp := (owner_spec m hm).2.2.1
    have e := room_spot ancs i ht ⟨c+m,by rw [hc]; omega⟩ (m:=m) rfl (by rw [hroles,role_count]; exact hm)
    simp only at e
    have := Set.mem_image_of_mem (shift (-d)) hsp
    simp only [Sum.elim_inr] at this
    rw [e] at this
    simp only [Gf,owner_eq m hm,spot]
    rw [hroom] at this
    exact this
  -- the cover
  let H : Set Point := ↑(G.image (shift (-d)))
  have cover : ∀ z∈(mapPoly (shift (-d)) PP).filled, ∃ g∈H, (mapPoly (shift (-d)) PP).Sees g z :=
    fun z hz => by simpa [H] using cover_shift hcov d z hz
  -- foreign guards
  have foreign : ∀ z∈(room n).filled, critical (1/(n:ℝ)) z → ∀ g∈H, (∀ m, m<4 → g≠Gf m) →
      ¬(mapPoly (shift (-d)) PP).Sees g z := by
    intro z hz hcz g hg hne
    obtain ⟨g0,hg0,rfl⟩ := Finset.mem_image.mp hg
    have cls := fun (zb : QBox) (hd : sep (0,1/20800,1,1) win zb=true) (hcl : corridorClear t.corridor win zb xmin=true)
        (hzb : zb.Mem z) => classify ne out ancs G hcov hevery i ht hok F hd hcl hz hzb g0 hg0
    have res : ¬(mapPoly (shift (-d)) PP).Sees (shift (-d) g0) z ∨
        ∃ k : Fin (PrivateRoles.records eqs i).length, c≤(k:Nat) ∧
          (PP).Sees g0 ((PrivateRoles.group eqs ancs).mark ⟨i,k⟩) ∧ g0∈(PrivateRoles.group eqs ancs).spot ⟨i,k⟩ := by
      exact cls box1 door1 clear1 (critical_box hn hcz)
    rcases res with blind|⟨k,hk,hsees,-⟩
    · exact blind
    · exfalso
      have hm : (k:Nat)-c<4 := by have := k.isLt; omega
      apply hne _ hm
      have u := (owner_spec _ hm).2.2.2 g0 hg0
      have kk : role ((k:Nat)-c) hm=⟨i,k⟩ :=
        congrArg (Sigma.mk i) (Fin.ext (by show c+((k:Nat)-c)=(k:Nat); omega))
      have e := u (by rw [kk]; exact hsees)
      simp only [Gf,owner_eq _ hm]
      rw [←e]
  -- the parameters of the four room guards
  have param (m : Nat) (hm : m<4) : ∃ τ : ℝ, (0≤τ ∧ τ≤3/2) ∧ Gf m=guard (1/(n:ℝ)) m τ := by
    obtain ⟨τ,hτ,e⟩ := slot_of_mem (pins m hm)
    exact ⟨τ,hτ,e⟩
  obtain ⟨tx,hx,gx⟩ := param 0 (by norm_num)
  obtain ⟨ty,hy,gy⟩ := param 1 (by norm_num)
  have rx : InRange (tx+1/2) := ⟨by linarith,by linarith⟩
  have ry : InRange (ty+1/2) := ⟨by linarith,by linarith⟩
  refine ⟨tx+1/2,ty+1/2,rx,ry,?_,joined_forces n hn _ tree H Gf pins cover foreign _ _ rx ry
    (by rw [gx]; congr 1; ring) (by rw [gy]; congr 1; ring)⟩
  -- the owners
  intro k m t' hk hmt p hp sees
  have hm : m<4 := by rcases hmt with ⟨rfl,-⟩|⟨rfl,-⟩ <;> norm_num
  have kk : role m hm=⟨i,k⟩ := congrArg (Sigma.mk i) (Fin.ext (by show c+m=(k:Nat); omega))
  have u := (owner_spec m hm).2.2.2 p hp
  have e := u (by rw [kk]; exact sees)
  have pe : shift (-d) p=Gf m := by simp only [Gf,owner_eq m hm]; rw [←e]
  rw [pe]
  rcases hmt with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · rw [gx]; congr 1; ring
  · rw [gy]; congr 1; ring

end Main

end ArtGallery.Orthogonal.BoundaryPoint.RoomRow.InvRevGe
end
