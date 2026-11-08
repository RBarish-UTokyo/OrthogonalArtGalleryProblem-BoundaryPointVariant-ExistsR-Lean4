module

public import ArtGallery.Orthogonal.BoundaryPoint.PinContact
public import ArtGallery.Orthogonal.BoundaryPoint.PocketSight

/-! # A single private pocket viewed from the closed hub door
The pocket is a source rectangle. Its overlap with each other source
rectangle is verified to lie on the forward wall. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PortalWindow
open Set GridPins PinGridData GridParity GridAtom RoomGrid CorridorProgram ArtGallery.Orthogonal.Hard PerpendicularPin

structure Portal where
  pocket : Rect Nat
  tip : Index
  swap : Bool
  flip : Bool

def lower (axis : Bool) (r : Rect Nat) := if axis then r.2.2.1 else r.1
def upper (axis : Bool) (r : Rect Nat) := if axis then r.2.2.2 else r.2.1
def Portal.far (p : Portal) := if p.flip then upper (!p.swap) p.pocket else lower (!p.swap) p.pocket
def Portal.near (p : Portal) := if p.flip then lower (!p.swap) p.pocket else upper (!p.swap) p.pocket
def Portal.frame (p : Portal) : Frame := ⟨p.swap,false,p.flip⟩

def contactOK (p : Portal) (q : Rect Nat) : Bool :=
  let r := p.pocket
  let n := !p.swap
  decide (r.2.1<q.1 ∨ q.2.1<r.1 ∨ r.2.2.2<q.2.2.1 ∨ q.2.2.2<r.2.2.1 ∨
    ((p.near≤lower n r ∨ p.near≤lower n q) ∧ (upper n r≤p.near ∨ upper n q≤p.near)))

def Portal.Valid (p : Portal) (nx ny : Nat) (rs : List (Rect Nat)) : Prop :=
  p.pocket∈rs ∧ small nx ny p.tip ∧ component (!p.swap) p.tip=p.far ∧
  lower (!p.swap) p.pocket<upper (!p.swap) p.pocket ∧
  lower p.swap p.pocket≤component p.swap p.tip ∧ component p.swap p.tip≤upper p.swap p.pocket ∧
  (rest p.pocket rs).all (contactOK p)=true

instance (p : Portal) (nx ny : Nat) (rs : List (Rect Nat)) : Decidable (p.Valid nx ny rs) := by
  unfold Portal.Valid; infer_instance

def level (xs ys : List ℝ) (ax : Bool) (i : Nat) := (if ax then ys else xs).getD i 0
def Portal.T (p : Portal) (xs ys : List ℝ) (i : Nat) := level xs ys p.swap i
def Portal.N (p : Portal) (xs ys : List ℝ) (i : Nat) := signR p.flip (level xs ys (!p.swap) i)

private theorem cut_atom {p : Portal} {q : Rect Nat} {X Y : Nat} (h : contactOK p q=true)
    (in1 : inBox X Y p.pocket=true) (in2 : inBox X Y q=true) :
    component (!p.swap) (X,Y)=line p.near := by
  have b := of_decide_eq_true h
  have a := of_decide_eq_true in1
  have c := of_decide_eq_true in2
  cases e : p.swap <;> simp only [e,Bool.not_true,Bool.not_false,lower,upper,component,Bool.false_eq_true,ite_false,ite_true] at b ⊢ <;>
    unfold line at * <;> omega

private theorem iso {xs ys : List ℝ} (hx : xs.IsChain (·<·)) (hy : ys.IsChain (·<·)) (ax : Bool) :
    StrictMonoOn (level xs ys ax) {i | i<(if ax then ys else xs).length} := by
  cases ax <;> first | exact strictMonoOn_getD hx | exact strictMonoOn_getD hy

private theorem node (xs ys : List ℝ) (ax : Bool) (i : Index) :
    component ax (gridPt xs ys i)=level xs ys ax (component ax i) := by cases ax <;> rfl

private theorem inside_axis {xs ys : List ℝ} {r : Rect Nat} (ax : Bool) {z : Point} (h : z∈tile xs ys r) :
    level xs ys ax (lower ax r)≤component ax z ∧ component ax z≤level xs ys ax (upper ax r) := by
  cases ax with
  | false => exact ⟨h.1,h.2.1⟩
  | true => exact ⟨h.2.2.1,h.2.2.2⟩

private theorem valid_ends {r : Rect Nat} {xs ys : List ℝ} (v : ValidBox xs.length ys.length r) (ax : Bool) :
    lower ax r<(if ax then ys else xs).length ∧ upper ax r<(if ax then ys else xs).length := by
  cases ax with | false => exact ⟨v.1,v.2.1⟩ | true => exact v.2.2

private theorem atom_eq_level {xs ys : List ℝ} (hx : xs.IsChain (·<·)) (hy : ys.IsChain (·<·))
    (axis : Bool) {k : Nat} (small : k<(if axis then ys else xs).length) (q : Point)
    (hit : component axis (GridAtom.atom q.1 xs,GridAtom.atom q.2 ys)=line k) :
    component axis q=level xs ys axis k := by
  cases axis
  · exact (compare_line hx small _).2.mpr hit
  · exact (compare_line hy small _).2.mpr hit

/-- The last argument tests a specific viewer. The resulting exclusion uses
the whole physical union, including the room and the staircase. -/
theorem blocked {P : Polygon} {xs ys : List ℝ} {rs : List (Rect Nat)}
    (hx : xs.IsChain (·<·)) (hy : ys.IsChain (·<·)) (hfill : P.filled=cellsR xs ys rs)
    (boxes : ∀ r∈rs,ValidBox xs.length ys.length r)
    (p : Portal) (valid : p.Valid xs.length ys.length rs) {g : Point} :
    let w := gridPt xs ys p.tip
    let A := p.N xs ys p.near-p.N xs ys p.far
    let B := p.T xs ys (upper p.swap p.pocket)-p.T xs ys (lower p.swap p.pocket)
    ((p.frame.pt g).2<(p.frame.pt w).2 ∨
      (B < |(p.frame.pt g).1-(p.frame.pt w).1| ∧
       B*((p.frame.pt g).2-(p.frame.pt w).2) < |(p.frame.pt g).1-(p.frame.pt w).1| * A)) →
    ¬P.Sees w g := by
  obtain ⟨mem,indices,back,depth,tl,tr,contacts⟩ := valid
  let n := !p.swap
  let t := p.swap
  let w := gridPt xs ys p.tip
  let lo := lower t p.pocket
  let hi := upper t p.pocket
  let A := p.N xs ys p.near-p.N xs ys p.far
  let B := p.T xs ys hi-p.T xs ys lo
  have dims := boxes _ mem
  have hN := valid_ends (xs:=xs) (ys:=ys) dims n
  have hT := valid_ends (xs:=xs) (ys:=ys) dims t
  have htip : component t p.tip<(if t then ys else xs).length := by cases e : t <;> first | exact indices.1 | exact indices.2
  have monoT := (iso hx hy t).monotoneOn
  have floor := (iso hx hy n) hN.1 hN.2 depth
  have Apos : 0<A := by
    unfold A Portal.N Portal.near Portal.far
    cases sign : p.flip <;> simpa only [sign,signR,ite_true,Bool.false_eq_true,ite_false,sub_pos,neg_lt_neg_iff] using floor
  have alongT : p.T xs ys lo≤component t w ∧ component t w≤p.T xs ys hi := by
    rw [show component t w=level xs ys t (component t p.tip) from node ..]
    exact ⟨monoT hT.1 htip tl,monoT htip hT.2 tr⟩
  have wn : component n w=level xs ys n p.far := by rw [show component n w=level xs ys n (component n p.tip) from node ..,back]
  have belongs : w∈tile xs ys p.pocket := by
    have nb : level xs ys n (lower n p.pocket)≤component n w ∧ component n w≤level xs ys n (upper n p.pocket) := by
      rw [wn]; cases e : p.flip <;> simp only [Portal.far,e,ite_true,Bool.false_eq_true,ite_false] <;> exact ⟨by first | rfl | exact floor.le,by first | rfl | exact floor.le⟩
    cases s : p.swap
    · exact ⟨by simpa [Portal.T,t,lo,s,component,level,lower] using alongT.1,
        by simpa [Portal.T,t,hi,s,component,level,upper] using alongT.2,
        by simpa [n,s,component,level,lower] using nb.1,by simpa [n,s,component,level,upper] using nb.2⟩
    · exact ⟨by simpa [n,s,component,level,lower] using nb.1,by simpa [n,s,component,level,upper] using nb.2,
        by simpa [Portal.T,t,lo,s,component,level,lower] using alongT.1,by simpa [Portal.T,t,hi,s,component,level,upper] using alongT.2⟩
  have form (z : Point) : p.frame.pt z=(component t z,signR p.flip (component n z)) := by
    rw [chart_components]; rfl
  dsimp only
  intro test
  refine PocketSight.exclude (w:=w) (g:=g) (A:=A) (B:=B) (ChimneyRegion.cell_closed _ _ _ _) (closed_tiles _ _ _)
    (hfill.trans (split_tile xs ys mem)) p.frame belongs Apos ?_ ?_ test
  · intro z hz
    have bt := inside_axis t hz
    have bn := inside_axis n hz
    rw [form,form]
    constructor
    · rw [wn]; cases sign : p.flip <;> simpa only [Portal.far,signR,sign,ite_true,Bool.false_eq_true,ite_false,neg_le_neg_iff] using (by first | exact bn.1 | exact bn.2)
    · change |component t z-component t w|≤p.T xs ys hi-p.T xs ys lo
      change p.T xs ys lo ≤ component t z ∧ component t z ≤ p.T xs ys hi at bt
      exact abs_le.mpr ⟨by linarith [bt.1,alongT.2],by linarith [bt.2,alongT.1]⟩
  · rintro q ⟨inP,inRest⟩
    obtain ⟨r,hr,inside⟩ := inRest
    have other : r∈rs := (List.mem_filter.mp hr).1
    have atom1 := (tile_iff hx hy dims q).mp inP
    have atom2 := (tile_iff hx hy (boxes r other) q).mp inside
    have h := cut_atom (List.all_eq_true.mp contacts r hr) atom1 atom2
    have near_index : p.near<(if n then ys else xs).length := by cases e : p.flip <;> simp only [Portal.near,e,ite_true,Bool.false_eq_true,ite_false] <;> first | exact hN.1 | exact hN.2
    have coordinate := atom_eq_level hx hy n near_index q h
    rw [form,form,coordinate,wn]
    change _ = _ + (p.N xs ys p.near-p.N xs ys p.far)
    unfold Portal.N; ring

end ArtGallery.Orthogonal.BoundaryPoint.PortalWindow
end
