module

public import ArtGallery.Orthogonal.BoundaryPoint.SourceEntrances
public import ArtGallery.Orthogonal.BoundaryPoint.EdgeSew

/-! # Applying repeated subedge gluing to the word generator's actual list
The splice table used below is the rectangle generator's own table, with its
edge endpoints cast to reals. Its rows carry either zero paths or a single
proper inside-door path. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SourceSplice
open Set Geometry RectContour ContourJoin BoundaryChart ChartDrawing CompiledSize CatalogPlan
open WingSeparation SourceEntrances BankCoordinates

def row (eqs : List ETRINV.Constraint) (e : Vertex × Vertex) : EdgeSew.Row :=
  ⟨ratPoint e.1,ratPoint e.2,(((wings eqs).filter (compat (W (scale eqs)) e)).flatMap Prod.snd).map ratPoint⟩

def rows (eqs : List ETRINV.Constraint) := (edges eqs).map (row eqs)

theorem starts (eqs : List ETRINV.Constraint) : (edges eqs).map Prod.fst=hubPath eqs := by
  unfold edges
  apply List.map_fst_zip
  simp only [List.length_append,List.length_drop,List.length_take]; omega

theorem base (eqs : List ETRINV.Constraint) : EdgeSew.before [] (rows eqs)=RealizedDoors.hub eqs := by
  have same : (rows eqs).map EdgeSew.Row.start=(hubPath eqs).map ratPoint := by
    simp only [rows,List.map_map,Function.comp_def,row]
    simpa only [List.map_map,Function.comp_def] using congrArg (List.map ratPoint) (starts eqs)
  unfold EdgeSew.before
  rw [List.nil_append,same]
  rfl

private theorem core {α : Type} {path : List α} {x y : α} (len : 3≤path.length)
    (first : path.head?=some x) (last : path.getLast?=some y) :
    ∃ v z, path=(x::v)++[z,y] := by
  cases path with
  | nil => simp at len
  | cons a l =>
    obtain rfl : a=x := by simpa using first
    rcases List.eq_nil_or_concat' l with rfl|⟨t,b,rfl⟩
    · simp at len
    · have eq : b=y := by simpa only [←List.cons_append,List.getLast?_append,List.getLast?_singleton,Option.some_or,Option.some.injEq] using last
      subst y
      rcases List.eq_nil_or_concat' t with rfl|⟨v,z,rfl⟩
      · simp at len
      · exact ⟨v,z,by simp [List.append_assoc]⟩

private theorem on_edge {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance}
    (path : emitted eqs r j e) (simple : (RealizedDoors.wing e).Simple) :
    let edge := HubDoors.topEdge j
    let obj : EdgeSew.Row := ⟨ratPoint edge.1,ratPoint edge.2,e.2.map ratPoint⟩
    EdgeSew.Shape (RealizedDoors.hub eqs).filled obj := by
  dsimp only
  intro _
  let n := scale eqs
  let a : Point := ratPoint (HubDoors.topEdge j).1
  let b : Point := ratPoint (HubDoors.topEdge j).2
  let d : ℝ := (door j:ℝ)
  let w : ℝ := (W n:ℝ)
  let t := (1101/10-w)/(1401/10)
  let u : ℝ := (1101/10)/(1401/10)
  have ne : eqs≠[] := by intro z; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  have big : 65≤n := (scale_bounds ne).1
  have wPositive : 0<w := by dsimp [w,W]; push_cast; positivity
  have wSmall : w≤1/2 := by
    dsimp only [w]; rw [cast_W]; exact BankPitch.width_le_half (by exact_mod_cast (show 1≤n by omega))
  have X : lerp a b t=(d+w,1) := by
    dsimp [a,b,d,t,lerp,HubDoors.topEdge,ratPoint]
    push_cast; apply Prod.ext <;> dsimp <;> ring
  have Y : lerp a b u=(d,1) := by
    dsimp [a,b,d,u,lerp,HubDoors.topEdge,ratPoint]
    push_cast; apply Prod.ext <;> dsimp <;> ring
  obtain ⟨l,hit⟩ := RealizedDoors.extraction catalog n j r.1 r.2 path.2
  have ends := endpoints hit
  have hd : (e.2.map ratPoint).head?=some (d+w,1) := by
    simp only [List.head?_map,ends.1,Option.map_some,ratPoint,d,w,Rat.cast_add,Rat.cast_one]
  have tl : (e.2.map ratPoint).getLast?=some (d,1) := by
    simp only [List.getLast?_map,ends.2,Option.map_some,ratPoint,d,Rat.cast_one]
  obtain ⟨v,z,hform⟩ := core simple.1 hd tl
  refine ⟨t,u,v,z,by dsimp [t]; linarith,by dsimp [t,u]; linarith,by norm_num [u],?_,simple,?_⟩
  · change e.2.map ratPoint=(lerp a b t::v)++[z,lerp a b u]
    rwa [X,Y]
  · change (RealizedDoors.hub eqs).filled∩(RealizedDoors.wing e).filled=ArtGallery.segment (lerp a b t) (lerp a b u)
    rw [X,Y,RealizedDoors.intersection path,segment_comm (d+w,1) (d,1)]; rfl

def SimpleWings (eqs : List ETRINV.Constraint) := ∀ r j e,emitted eqs r j e → (RealizedDoors.wing e).Simple

theorem geometry {eqs : List ETRINV.Constraint} (all : SimpleWings eqs) {edge : Vertex × Vertex} (h : edge∈edges eqs) :
    EdgeSew.Shape (RealizedDoors.hub eqs).filled (row eqs edge) := by
  rcases one_or_none h with empty|⟨e,one,member,hit⟩
  · intro nonempty; simp [row,empty] at nonempty
  · obtain ⟨r,j,path,rfl⟩ := registered h member hit
    simpa only [row,one,List.flatMap_cons,List.flatMap_nil,List.append_nil] using on_edge path (all r j e path)

theorem independent {eqs : List ETRINV.Constraint} (ne : eqs≠[]) :
    (rows eqs).Pairwise (fun r s => Disjoint (EdgeSew.part r) (EdgeSew.part s)) := by
  have nodup : ((hubPath eqs).map ratPoint).Nodup := (SimplePaths.open_simple (RealizedHub.production ne)).nodup
  have edges_ne : (edges eqs).Pairwise (fun a b => ratPoint a.1 ≠ ratPoint b.1) := by
    rw [← starts eqs,List.map_map] at nodup
    exact List.pairwise_map.mp nodup
  apply List.pairwise_map.mpr
  apply edges_ne.imp_of_mem
  intro a b ha hb different
  rcases one_or_none ha with ea|⟨u,ua,um,uh⟩
  · simp [EdgeSew.part,row,ea]
  rcases one_or_none hb with eb|⟨v,vb,vm,vh⟩
  · simp [EdgeSew.part,row,eb]
  obtain ⟨r,i,atI,ia⟩ := registered ha um uh
  obtain ⟨s,j,atJ,jb⟩ := registered hb vm vh
  have sep : i≠j := by intro same; exact different (by rw [ia,jb,same])
  have disj := WingSeparation.disjoint atI atJ sep
  by_cases uz : u.2=[]
  · simp [EdgeSew.part,row,ua,uz]
  by_cases vz : v.2=[]
  · simp [EdgeSew.part,row,vb,vz]
  simpa [EdgeSew.part,EdgeSew.wing,row,ua,vb,uz,vz] using disj

private theorem linked (f : Vertex × Vertex → EdgeSew.Row)
    (start : ∀ a b,(f (a,b)).start=ratPoint a) (stop : ∀ a b,(f (a,b)).stop=ratPoint b)
    (a close : Vertex) (l : List Vertex) (last : ∀ b,(f (b,close)).path=[]) :
    EdgeSew.successive (((a::l).zip (l++[close])).map f) := by
  induction l generalizing a with
  | nil => exact last a
  | cons b l ih =>
    cases l with
    | nil => exact ⟨(stop a b).trans (start b close).symm,last b⟩
    | cons c l => exact ⟨(stop a b).trans (start b c).symm,ih b⟩

theorem successive {eqs : List ETRINV.Constraint} (ne : eqs≠[]) : EdgeSew.successive (rows eqs) := by
  let n := scale eqs
  let a : Vertex := (door ((compile eqs).1.length-1)-30-1/10,1-D n)
  have hub : hubPath eqs=a::(hubPath eqs).tail := rfl
  have hd : 0<D n := by
    have natural : 65≤n := (scale_bounds ne).1
    unfold D BankCoordinates.k; positivity
  have closed : a.2≠1 := by dsimp [a]; linarith
  have last (b : Vertex) : (row eqs (b,a)).path=[] := by
    have H : ∀ e∈wings eqs, ¬ compat (W n) (b,a) e=true := by intro e _; simp [compat,closed]
    have no := List.filter_eq_nil_iff.mpr H
    simp only [row,show W (scale eqs)=W n by rfl,no,List.flatMap_nil,List.map_nil]
  unfold rows edges
  rw [hub]
  simpa only [List.take_succ_cons,List.take_zero,List.drop_succ_cons,List.drop_zero] using
    linked (row eqs) (fun _ _ => rfl) (fun _ _ => rfl) a a (hubPath eqs).tail last

theorem assembly {eqs : List ETRINV.Constraint} (ne : eqs≠[]) (all : SimpleWings eqs) :
    EdgeSew.Joined [] (rows eqs) := by
  apply EdgeSew.assemble
  · rw [base]; exact RealizedHub.production ne
  · exact successive ne
  · intro r hr; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    rw [base]; exact geometry all he
  · exact independent ne

theorem output {eqs : List ETRINV.Constraint} {v : List Vertex}
    (hit : splice (W (scale eqs)) (hubPath eqs) (wings eqs)=some v) :
    EdgeSew.after [] (rows eqs)=⟨v.map ratPoint⟩ := by
  unfold splice at hit; dsimp only at hit
  split at hit
  · obtain rfl := Option.some.inj hit
    simp only [EdgeSew.after,rows,List.nil_append,sections,edges,List.flatMap_map,List.map_flatMap,row,
      Function.comp_def,List.flatMap_def,List.map_cons,List.map_flatten,List.map_map,Function.comp_apply]
  · cases hit

end ArtGallery.Orthogonal.BoundaryPoint.SourceSplice
end
