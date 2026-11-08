module

public import ArtGallery.Orthogonal.BoundaryPoint.RealizedHub

/-! # Exactly one registered wing on each active ceiling edge -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SourceEntrances
open CatalogPlan CompiledSize ChartDrawing BankCoordinates ContourJoin BoundaryChart RectContour WingSeparation

def wings (eqs : List ETRINV.Constraint) : List Entrance := (batch (scale eqs) (compile eqs).1).filterMap Prod.fst
def hubPath (eqs : List ETRINV.Constraint) : List Vertex :=
  hubCycle (scale eqs) (compile eqs).1.length (PlacedSlots.starts eqs)
def edges (eqs : List ETRINV.Constraint) :=
  let h := hubPath eqs
  h.zip (h.drop 1++h.take 1)

theorem present {eqs : List ETRINV.Constraint} {e : Entrance} :
    e∈wings eqs ↔ ∃ r j,emitted eqs r j e := by
  constructor
  · intro h
    obtain ⟨d,hd,out⟩ := List.mem_filterMap.mp h
    obtain ⟨⟨r,j⟩,hj,rfl⟩ := List.mem_map.mp hd
    exact ⟨r,j,hj,out⟩
  · rintro ⟨r,j,hj,out⟩
    exact List.mem_filterMap.mpr ⟨_,List.mem_map.mpr ⟨(r,j),hj,rfl⟩,out⟩

theorem distinct (eqs : List ETRINV.Constraint) : (wings eqs).Pairwise (fun a b => a.1≠b.1) := by
  let rows := (compile eqs).1
  let fn (u : Row × Nat) := (choose catalog (fun t => drawOne t (scale eqs) u.2 u.1.2) u.1.1 (none,0)).1
  have increasing : rows.zipIdx.Pairwise (fun a b => a.2<b.2) := by
    apply (List.pairwise_map (f:=Prod.snd) (R:=(·<·))).mp
    rw [List.zipIdx_map_snd]
    exact List.pairwise_lt_range' 1 (by decide)
  change ((rows.zipIdx.map _).filterMap Prod.fst).Pairwise _
  rw [List.filterMap_map]
  change (rows.zipIdx.filterMap fn).Pairwise _
  apply List.pairwise_filterMap.mpr
  apply increasing.imp_of_mem
  intro a b ha hb order e he f hf
  have A := (placement (r:=a.1) (j:=a.2) (e:=e) (eqs:=eqs) ⟨ha,he⟩).1
  have B := (placement (r:=b.1) (j:=b.2) (e:=f) (eqs:=eqs) ⟨hb,hf⟩).1
  rw [A,B]
  unfold door
  exact (mul_lt_mul_of_neg_left (by exact_mod_cast order) (by norm_num : (-2000:ℚ)<0)).ne'

theorem registered {eqs : List ETRINV.Constraint} {edge : Vertex × Vertex} (he : edge∈edges eqs) {e : Entrance}
    (member : e∈wings eqs) (matchDoor : compat (W (scale eqs)) edge e=true) :
    ∃ r j,emitted eqs r j e ∧ edge=HubDoors.topEdge j := by
  obtain ⟨r,j,path⟩ := present.mp member
  have ne : eqs≠[] := by intro z; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  have hn := (scale_bounds ne).1
  have high : HubDoors.high edge=true := by
    simp only [compat,Bool.and_eq_true] at matchDoor
    simpa only [HubDoors.high,Bool.and_eq_true] using matchDoor.1.1.1
  have listed := List.mem_filter.mpr ⟨he,high⟩
  rw [show (edges eqs).filter HubDoors.high=(List.range (compile eqs).1.length).map HubDoors.topEdge from
    HubDoors.ceiling _ _ _ hn] at listed
  obtain ⟨k,hk,eq⟩ := List.mem_map.mp listed
  have A := (placement path).1
  have same : compat (W (scale eqs)) (HubDoors.topEdge k) (door j,e.2)=true := by
    simpa only [eq,←A,Prod.mk.eta] using matchDoor
  rw [HubDoors.slot _ _ _ hn] at same
  obtain rfl := beq_iff_eq.mp same
  exact ⟨r,j,path,eq.symm⟩

private theorem top_injective : Function.Injective HubDoors.topEdge := by
  intro a b eq
  have h := congrArg (fun e : Vertex × Vertex => e.2.1) eq
  change -2000*(a:ℚ)-30 = -2000*(b:ℚ)-30 at h
  exact_mod_cast (show (a:ℚ)=b by linarith)

theorem one_or_none {eqs : List ETRINV.Constraint} {edge : Vertex × Vertex} (he : edge∈edges eqs) :
    let active := (wings eqs).filter (compat (W (scale eqs)) edge)
    active=[] ∨ ∃ e,active=[e] ∧ e∈wings eqs ∧ compat (W (scale eqs)) edge e=true := by
  let active := (wings eqs).filter (compat (W (scale eqs)) edge)
  have all : ∀ e∈active,e∈wings eqs ∧ compat (W (scale eqs)) edge e=true := fun _ h => List.mem_filter.mp h
  have one (a b : Entrance) (ha : a∈active) (hb : b∈active) : a.1=b.1 := by
    obtain ⟨r,j,pa,ea⟩ := registered he (all _ ha).1 (all _ ha).2
    obtain ⟨s,k,pb,eb⟩ := registered he (all _ hb).1 (all _ hb).2
    rw [(placement pa).1,(placement pb).1,top_injective (ea.symm.trans eb)]
  have ordered : active.Pairwise (fun a b => a.1≠b.1) := (distinct eqs).filter _
  change active=[] ∨ _
  cases eq : active with
  | nil => exact Or.inl rfl
  | cons a t =>
    have A : a∈active := eq ▸ List.mem_cons_self
    cases t with
    | nil => exact Or.inr ⟨a,eq,all a A⟩
    | cons b bs =>
      have B : b∈active := eq ▸ List.mem_cons_of_mem a List.mem_cons_self
      rw [eq] at ordered
      exact ((List.pairwise_cons.mp ordered).1 b List.mem_cons_self (one a b A B)).elim

theorem endpoints {l path : List Vertex} {d w : ℚ} (out : atDoor d w l=some path) :
    path.head?=some (d+w,1) ∧ path.getLast?=some (d,1) := by
  let i := l.idxOf (0,1)
  unfold atDoor at out
  dsimp only at out
  split at out
  · contradiction
  next good =>
    have H : ¬((decide (i ≥ l.length) || (l.getD ((i+1) % l.length) (0,0) != (w,1)))=true) := good
    have hi : i<l.length := by by_contra! k; simp [k] at H
    have succPoint : l.getD ((i+1)%l.length) (0,0)=(w,1) := by
      simpa only [Nat.not_le.mpr hi,decide_false,Bool.false_or,bne_iff_ne,not_not] using H
    let ls := l.drop (i+1)
    let rs := l.take (i+1)
    have old : l[i]=(0,1) := List.getElem_idxOf hi
    have lastR : rs.getLast?=some (0,1) := by
      simp only [rs,List.getLast?_take,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel,
        List.getElem?_eq_getElem hi,Option.some_or,old]
    have firstLR : (ls++rs).head?=some (w,1) := by
      rw [List.head?_append]
      by_cases k : i+1<l.length
      · have pos : l[i+1]=(w,1) := by
          rw [Nat.mod_eq_of_lt k,List.getD_eq_getElem _ _ k] at succPoint; exact succPoint
        simp [ls,List.getElem?_eq_getElem k,pos]
      · have eq : i+1=l.length := by omega
        have z : 0<l.length := by omega
        have pos : l[0]=(w,1) := by simpa only [eq,Nat.mod_self,List.getD_eq_getElem _ _ z] using succPoint
        simp [ls,rs,eq,List.head?_eq_getElem?,List.getElem?_eq_getElem z,pos]
    obtain rfl := Option.some.inj out
    change ((ls++rs).map _).head?=_ ∧ ((ls++rs).map _).getLast?=_
    rw [List.head?_map,firstLR,List.getLast?_map,List.getLast?_append,lastR]
    simp [add_comm]

end ArtGallery.Orthogonal.BoundaryPoint.SourceEntrances
end
