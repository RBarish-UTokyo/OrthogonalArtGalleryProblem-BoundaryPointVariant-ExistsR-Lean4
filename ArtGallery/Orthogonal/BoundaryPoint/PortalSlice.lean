module

public import ArtGallery.Orthogonal.BoundaryPoint.PortalGate
public import ArtGallery.Orthogonal.BoundaryPoint.SlabSight

/-! # A horizontal section blocking both shaft witnesses of an inverse axis -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PortalSlice
open PinGridData Set PortalGate PortalWindow GridParity GridPins RoomGrid IndexedWing RegisterForm RegisterOrder
open RegisterTable MarginCert LinearRegister ChartDrawing CorridorProgram ArtGallery.Orthogonal.Hard

structure Cut where
  tip : Index
  row : Nat
  left : Nat
  heightPower : Nat
  productHint : RegisterProduct.Hint

def Cut.valid (c : Cut) (nx ny : Nat) (rs : List (Rect Nat)) : Prop :=
  c.tip.1<nx ∧ c.tip.2<c.row ∧ c.row<ny ∧ c.left<nx ∧
    ∀ r∈rs,r.2.2.2<c.row ∨ c.row<r.2.2.1 ∨ c.left≤r.1

instance (c : Cut) (nx ny : Nat) (rs : List (Rect Nat)) : Decidable (c.valid nx ny rs) := by
  unfold Cut.valid; infer_instance

def xGap (c : Cut) : Delta := (.level false c.left,.high false)
def rise (c : Cut) : Delta := (.level true c.row,.level true c.tip.2)
def tailX (c : Cut) : Delta := (.level false c.tip.1,.level false c.left)
def topY (c : Cut) : Delta := (.high true,.level true c.row)
def Cut.check (c : Cut) (t : Template) (bs : List Box) (cache : List Entry) :=
  positive (atomBox bs) ((topY c).form t cache) c.heightPower &&
  RegisterProduct.check (atomBox bs) ((xGap c).form t cache) ((rise c).form t cache)
    ((tailX c).form t cache) ((topY c).form t cache) c.productHint

theorem below {y h x l r v : ℝ} (lower : y<h) (upper : h<1) (vx : v≤r)
    (prod : (x-l)*(1-h)<(l-r)*(h-y)) : SlabSight.height y x 1 v h < l := by
  have den : 0<1-y := sub_pos.mpr (lower.trans upper)
  have hpos : 0≤(h-y)/(1-y) := div_nonneg (sub_nonneg.mpr lower.le) den.le
  have dominant : SlabSight.height y x 1 v h ≤ SlabSight.height y x 1 r h :=
    add_le_add (le_refl x) (mul_le_mul_of_nonneg_left (sub_le_sub_right vx x) hpos)
  apply dominant.trans_lt
  unfold SlabSight.height
  rw [div_mul_eq_mul_div,←lt_sub_iff_add_lt',div_lt_iff₀ den]
  linarith only [show (r-x)*(h-y)<(l-x)*(1-y) by linarith only [prod]]

theorem misses {t : Template} {args xs rows bs cache} (m : Model args xs rows bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest))
    {P : Polygon} {rs : List (Rect Nat)} (c : Cut)
    (valid : c.valid t.chart.x.length t.chart.y.length rs)
    (boxes : ∀ r∈rs,ValidBox t.chart.x.length t.chart.y.length r) (pass : c.check t bs cache=true) :
    let X := (grid t args false).map ((↑) : ℚ → ℝ)
    let Y := (grid t args true).map ((↑) : ℚ → ℝ)
    X.IsChain (·<·) → Y.IsChain (·<·) → P.filled=cellsR X Y rs →
    ∀ g, Door (getRat args 0) g → ¬P.Sees (gridPt X Y c.tip) g := by
  let X := (grid t args false).map ((↑) : ℚ → ℝ)
  let Y := (grid t args true).map ((↑) : ℚ → ℝ)
  have xl : X.length=t.chart.x.length := by simp [X,grid,BoundaryChart.selected,idsOf]
  have yl : Y.length=t.chart.y.length := by simp [Y,grid,BoundaryChart.selected,idsOf]
  rw [←xl,←yl] at valid boxes
  obtain ⟨sx,ly,sy,cx,side⟩ := valid
  obtain ⟨upperOK,prodOK⟩ := Bool.and_eq_true_iff.mp pass
  have pos := positive_value (atom_bound m.bounds) m.pos m.upper upperOK
  have cp := RegisterProduct.compare (atom_bound m.bounds) m.pos m.upper c.productHint prodOK
  have top : 0<1-Y.getD c.row 0 := by
    simpa only [delta_value m run,Rat.cast_zero,topY,Delta.real,Node.real,level,ite_true] using (Rat.cast_lt (K:=ℝ)).mpr pos
  have prod : (X.getD c.tip.1 0-X.getD c.left 0)*(1-Y.getD c.row 0) <
      (X.getD c.left 0-(getRat args 0:ℝ)/320)*(Y.getD c.row 0-Y.getD c.tip.2 0) := by
    simpa only [Rat.cast_mul,delta_value m run,xGap,rise,tailX,topY,Delta.real,Node.real,level,ite_true,Bool.false_eq_true,ite_false] using (Rat.cast_lt (K:=ℝ)).mpr cp
  dsimp only; intro hx hy region g gate saw
  let w := gridPt X Y c.tip
  let h := Y.getD c.row 0
  have lower : w.2<h := strictMonoOn_getD hy (ly.trans sy) sy ly
  have upper : h<1 := sub_pos.mp top
  have between : h∈uIcc w.2 (1:ℝ) := Set.uIcc_of_le (lower.trans upper).le ▸ ⟨lower.le,upper.le⟩
  let a := SlabSight.height w.2 w.1 1 g.1 h
  have cut : (a,h)∈P.filled := by
    apply saw
    rw [show g=(g.1,1) from Prod.ext rfl gate.2.2]
    exact SlabSight.path (lower.trans upper).ne between true
  rw [region] at cut
  obtain ⟨r,mem,inBox⟩ := cut
  have size := boxes r mem
  have bound : X.getD c.left 0 ≤ a := by
    rcases side r mem with v|v|v
    · exact ((strictMonoOn_getD hy size.2.2.2 sy v).not_ge inBox.2.2.2).elim
    · exact ((strictMonoOn_getD hy sy size.2.2.1 v).not_ge inBox.2.2.1).elim
    · exact ((strictMonoOn_getD hx).monotoneOn cx size.1 v).trans inBox.1
  exact (below lower upper gate.2.1 prod).not_ge bound

end ArtGallery.Orthogonal.BoundaryPoint.PortalSlice
end
