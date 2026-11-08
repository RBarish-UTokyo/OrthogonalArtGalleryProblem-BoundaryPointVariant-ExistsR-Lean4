module

public import Mathlib.Tactic.IntervalCases

public import ArtGallery.Orthogonal.BoundaryPoint.HubJoinTotal
public import ArtGallery.Orthogonal.BoundaryPoint.CompiledAddresses
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.Lower_10_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.Lower_10_360_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.Lower_10_520_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.InvLe_1_360
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.InvLe_1_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.InvRevGe_40_200

/-! # Total emission on all well-formed bounded ETR-INV instances
The physical chart prefix check supplies each wing path. Its door always
matches exactly one step of the hub, so every valid source produces a vertex
list and guard budget, irrespective of its arithmetic feasibility. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CandidateTotal
open PrivatePorts CatalogPlan CatalogLogic CatalogRanks CompiledSize CompiledAddresses
open ChartDrawing BoundaryChart RectContour ContourJoin BankCoordinates

private theorem two (l : List Nat) (h : l.length=2) : ∃ a b,l=[a,b] := by
  rcases l with _|⟨a,l⟩; simp at h
  rcases l with _|⟨b,l⟩; simp at h
  have eq : l=[] := by simpa using h
  exact ⟨a,b,eq ▸ rfl⟩

private theorem three (l : List Nat) (h : l.length=3) : ∃ a b c,l=[a,b,c] := by
  rcases l with _|⟨a,l⟩; simp at h
  obtain ⟨b,c,rfl⟩ := two l (by simpa using h)
  exact ⟨a,b,c,rfl⟩

private theorem style_bound {ι ρ} (l : Leaf (Slot ι ρ)) : style l<14 := by
  cases l <;> simp only [style] <;> (try split_ifs) <;> norm_num

theorem valid_row {eqs : List ETRINV.Constraint} {r : Row} (hr : r∈(compile eqs).1) :
    r.1<14 ∧ r.2.length=(profileBanks r.1).length := by
  change r∈(expanded eqs).map (fun q => (q.1,q.2.map (CatalogPlan.rank (keysOf eqs)))) at hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  refine ⟨?_,by simp only [expanded_banks eqs q hq,List.length_map]⟩
  obtain ⟨⟨e,j⟩,_,h⟩ := List.mem_flatMap.mp hq
  change q∈expand j e at h
  rw [expand_eq] at h
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp h
  obtain ⟨l,_,rfl⟩ := List.mem_map.mp hw
  exact style_bound l

private theorem from_open (t : Template) (n j : Nat) (rs : List Nat)
    (h : let s := (1:ℚ)/n
      let data := t.corridor.coords (s::((j:ℚ)*s)::(rs.map fun (r : Nat) => (r:ℚ)*s))
      let extra := t.room.coords s
      (atDoor (door j) (W n) (t.chart.draw (data.1++extra.1,data.2++extra.2))).isSome=true) :
    (drawOne t n j rs).1.isSome=true := by simpa only [drawOne,Option.isSome_map] using h

theorem safe (n j tag : Nat) (rs : List Nat) (hn : 65≤n) (hj : j≤n)
    (valid : tag<14) (arity : rs.length=(profileBanks tag).length) (bounds : ∀ r∈rs,r≤n) :
    (choose catalog (fun t => drawOne t n j rs) tag (none,0)).1.isSome=true := by
  interval_cases tag
  · obtain ⟨i0,i1,i2,rfl⟩ := three rs arity
    let t : Template := ⟨BankCorridor.Ordinary_40_200_520.layout,⟨RoomFamily.Ordinary.xAxis,RoomFamily.Ordinary.yAxis,RoomFamily.Ordinary.cells,RoomFamily.Ordinary.roles⟩,WingChart.Ordinary_40_200_520.chart⟩
    change (drawOne t n j [i0,i1,i2]).1.isSome=true
    apply from_open
    exact WingDoor.Ordinary_40_200_520.opens n j i0 i1 i2 hn hj (bounds i0 (by simp)) (bounds i1 (by simp)) (bounds i2 (by simp)) (t.room.coords (1/n))
  · obtain ⟨i0,i1,i2,rfl⟩ := three rs arity
    let t : Template := ⟨BankCorridor.Shifted_40_200_520.layout,⟨RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,RoomFamily.Shifted.cells,RoomFamily.Shifted.roles⟩,WingChart.Shifted_40_200_520.chart⟩
    change (drawOne t n j [i0,i1,i2]).1.isSome=true
    apply from_open
    exact WingDoor.Shifted_40_200_520.opens n j i0 i1 i2 hn hj (bounds i0 (by simp)) (bounds i1 (by simp)) (bounds i2 (by simp)) (t.room.coords (1/n))
  · obtain ⟨i0,i1,i2,rfl⟩ := three rs arity
    let t : Template := ⟨BankCorridor.Lower_40_200_1000.layout,⟨RoomFamily.Lower.xAxis,RoomFamily.Lower.yAxis,RoomFamily.Lower.cells,RoomFamily.Lower.roles⟩,WingChart.Lower_40_200_1000.chart⟩
    change (drawOne t n j [i0,i1,i2]).1.isSome=true
    apply from_open
    exact WingDoor.Lower_40_200_1000.opens n j i0 i1 i2 hn hj (bounds i0 (by simp)) (bounds i1 (by simp)) (bounds i2 (by simp)) (t.room.coords (1/n))
  · obtain ⟨i0,i1,i2,rfl⟩ := three rs arity
    let t : Template := ⟨BankCorridor.Lower_10_40_1000.layout,⟨RoomFamily.Lower.xAxis,RoomFamily.Lower.yAxis,RoomFamily.Lower.cells,RoomFamily.Lower.roles⟩,WingChart.Lower_10_40_1000.chart⟩
    change (drawOne t n j [i0,i1,i2]).1.isSome=true
    apply from_open
    exact WingDoor.Lower_10_40_1000.opens n j i0 i1 i2 hn hj (bounds i0 (by simp)) (bounds i1 (by simp)) (bounds i2 (by simp)) (t.room.coords (1/n))
  · obtain ⟨i0,i1,i2,rfl⟩ := three rs arity
    let t : Template := ⟨BankCorridor.Lower_10_200_1000.layout,⟨RoomFamily.Lower.xAxis,RoomFamily.Lower.yAxis,RoomFamily.Lower.cells,RoomFamily.Lower.roles⟩,WingChart.Lower_10_200_1000.chart⟩
    change (drawOne t n j [i0,i1,i2]).1.isSome=true
    apply from_open
    exact WingDoor.Lower_10_200_1000.opens n j i0 i1 i2 hn hj (bounds i0 (by simp)) (bounds i1 (by simp)) (bounds i2 (by simp)) (t.room.coords (1/n))
  · obtain ⟨i0,i1,i2,rfl⟩ := three rs arity
    let t : Template := ⟨BankCorridor.Lower_10_360_1000.layout,⟨RoomFamily.Lower.xAxis,RoomFamily.Lower.yAxis,RoomFamily.Lower.cells,RoomFamily.Lower.roles⟩,WingChart.Lower_10_360_1000.chart⟩
    change (drawOne t n j [i0,i1,i2]).1.isSome=true
    apply from_open
    exact WingDoor.Lower_10_360_1000.opens n j i0 i1 i2 hn hj (bounds i0 (by simp)) (bounds i1 (by simp)) (bounds i2 (by simp)) (t.room.coords (1/n))
  · obtain ⟨i0,i1,i2,rfl⟩ := three rs arity
    let t : Template := ⟨BankCorridor.Lower_10_520_1000.layout,⟨RoomFamily.Lower.xAxis,RoomFamily.Lower.yAxis,RoomFamily.Lower.cells,RoomFamily.Lower.roles⟩,WingChart.Lower_10_520_1000.chart⟩
    change (drawOne t n j [i0,i1,i2]).1.isSome=true
    apply from_open
    exact WingDoor.Lower_10_520_1000.opens n j i0 i1 i2 hn hj (bounds i0 (by simp)) (bounds i1 (by simp)) (bounds i2 (by simp)) (t.room.coords (1/n))
  · obtain ⟨i0,i1,rfl⟩ := two rs arity
    let t : Template := ⟨BankCorridor.InvLe_1_40.layout,⟨RoomFamily.InvLe.xAxis,RoomFamily.InvLe.yAxis,RoomFamily.InvLe.cells,RoomFamily.InvLe.roles⟩,WingChart.InvLe_1_40.chart⟩
    change (drawOne t n j [i0,i1]).1.isSome=true
    apply from_open
    exact WingDoor.InvLe_1_40.opens n j i0 i1 hn hj (bounds i0 (by simp)) (bounds i1 (by simp)) (t.room.coords (1/n))
  · obtain ⟨i0,i1,rfl⟩ := two rs arity
    let t : Template := ⟨BankCorridor.InvLe_1_200.layout,⟨RoomFamily.InvLe.xAxis,RoomFamily.InvLe.yAxis,RoomFamily.InvLe.cells,RoomFamily.InvLe.roles⟩,WingChart.InvLe_1_200.chart⟩
    change (drawOne t n j [i0,i1]).1.isSome=true
    apply from_open
    exact WingDoor.InvLe_1_200.opens n j i0 i1 hn hj (bounds i0 (by simp)) (bounds i1 (by simp)) (t.room.coords (1/n))
  · obtain ⟨i0,i1,rfl⟩ := two rs arity
    let t : Template := ⟨BankCorridor.InvLe_1_360.layout,⟨RoomFamily.InvLe.xAxis,RoomFamily.InvLe.yAxis,RoomFamily.InvLe.cells,RoomFamily.InvLe.roles⟩,WingChart.InvLe_1_360.chart⟩
    change (drawOne t n j [i0,i1]).1.isSome=true
    apply from_open
    exact WingDoor.InvLe_1_360.opens n j i0 i1 hn hj (bounds i0 (by simp)) (bounds i1 (by simp)) (t.room.coords (1/n))
  · obtain ⟨i0,i1,rfl⟩ := two rs arity
    let t : Template := ⟨BankCorridor.InvLe_1_520.layout,⟨RoomFamily.InvLe.xAxis,RoomFamily.InvLe.yAxis,RoomFamily.InvLe.cells,RoomFamily.InvLe.roles⟩,WingChart.InvLe_1_520.chart⟩
    change (drawOne t n j [i0,i1]).1.isSome=true
    apply from_open
    exact WingDoor.InvLe_1_520.opens n j i0 i1 hn hj (bounds i0 (by simp)) (bounds i1 (by simp)) (t.room.coords (1/n))
  · obtain ⟨i0,i1,rfl⟩ := two rs arity
    let t : Template := ⟨BankCorridor.InvRevGe_1_10.layout,⟨RoomFamily.InvRevGe.xAxis,RoomFamily.InvRevGe.yAxis,RoomFamily.InvRevGe.cells,RoomFamily.InvRevGe.roles⟩,WingChart.InvRevGe_1_10.chart⟩
    change (drawOne t n j [i0,i1]).1.isSome=true
    apply from_open
    exact WingDoor.InvRevGe_1_10.opens n j i0 i1 hn hj (bounds i0 (by simp)) (bounds i1 (by simp)) (t.room.coords (1/n))
  · obtain ⟨i0,i1,rfl⟩ := two rs arity
    let t : Template := ⟨BankCorridor.InvLe_40_200.layout,⟨RoomFamily.InvLe.xAxis,RoomFamily.InvLe.yAxis,RoomFamily.InvLe.cells,RoomFamily.InvLe.roles⟩,WingChart.InvLe_40_200.chart⟩
    change (drawOne t n j [i0,i1]).1.isSome=true
    apply from_open
    exact WingDoor.InvLe_40_200.opens n j i0 i1 hn hj (bounds i0 (by simp)) (bounds i1 (by simp)) (t.room.coords (1/n))
  · obtain ⟨i0,i1,rfl⟩ := two rs arity
    let t : Template := ⟨BankCorridor.InvRevGe_40_200.layout,⟨RoomFamily.InvRevGe.xAxis,RoomFamily.InvRevGe.yAxis,RoomFamily.InvRevGe.cells,RoomFamily.InvRevGe.roles⟩,WingChart.InvRevGe_40_200.chart⟩
    change (drawOne t n j [i0,i1]).1.isSome=true
    apply from_open
    exact WingDoor.InvRevGe_40_200.opens n j i0 i1 hn hj (bounds i0 (by simp)) (bounds i1 (by simp)) (t.room.coords (1/n))

private theorem address_of_path (ts : List Template) (n j i : Nat) (ranks : List Nat) {e : Entrance}
    (h : (choose ts (fun t => drawOne t n j ranks) i (none,0)).1=some e) : e.1=door j := by
  induction ts generalizing i with
  | nil => contradiction
  | cons t ts ih =>
    simp only [choose] at h
    split at h
    · obtain ⟨w,_,rfl⟩ := Option.map_eq_some_iff.mp h
      rfl
    · exact ih _ h

theorem emitted (eqs : List ETRINV.Constraint) : (CandidateWord.vertices eqs).isSome=true := by
  by_cases empty : eqs=[]
  · subst eqs; rfl
  let p := compile eqs
  let n := scale eqs
  have big : 65≤n := (scale_bounds empty).1
  have nrows := (row_bounds eqs).1
  have nonempty : p.1≠[] := by
    have m := List.length_pos_iff.mpr empty
    intro no
    change 65*eqs.length≤p.1.length at nrows
    rw [no,List.length_nil] at nrows
    omega
  let paths := batch n p.1
  have all : paths.all (fun r => r.1.isSome)=true := by
    apply List.all_eq_true.mpr
    intro a ha
    obtain ⟨⟨r,j⟩,hj,rfl⟩ := List.mem_map.mp ha
    have member : r∈p.1 := List.fst_mem_of_mem_zipIdx hj
    have v := valid_row member
    exact safe _ _ _ _ big (program_door eqs hj).le v.1 v.2 (fun _ h => (program_ranks eqs member h).le)
  have doors : ∀ e∈paths.filterMap Prod.fst,∃ i,i<p.1.length ∧ e.1=door i := by
    intro e he
    obtain ⟨w,hw,path⟩ := List.mem_filterMap.mp he
    obtain ⟨⟨r,j⟩,hj,rfl⟩ := List.mem_map.mp hw
    exact ⟨j,(List.mem_zipIdx' hj).1,address_of_path _ n _ _ _ path⟩
  let slots := p.2.map (fun a => slotX n a.1 a.2)
  have joined := HubJoinTotal.accepts n p.1.length big slots (paths.filterMap Prod.fst) doors
  change (ChartDrawing.vertices p).isSome=true
  unfold ChartDrawing.vertices
  have ne : p.1.isEmpty=false := by simpa using nonempty
  simp only [ne,Bool.false_eq_true,ite_false]
  change (if paths.all (fun w => w.1.isSome) then
    (splice (W n) (hubCycle n p.1.length slots) (paths.filterMap Prod.fst)).map _ else none).isSome=true
  simpa only [all,ite_true,Option.isSome_map] using joined

theorem exists_vertices (eqs : List ETRINV.Constraint) :
    ∃ v g,CandidateWord.vertices eqs=some (v,g) := by
  have ok := emitted eqs
  cases h : CandidateWord.vertices eqs with
  | none => simp [h] at ok
  | some v => exact ⟨v.1,v.2,rfl⟩

end ArtGallery.Orthogonal.BoundaryPoint.CandidateTotal
end
