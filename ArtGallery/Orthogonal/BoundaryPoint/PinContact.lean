module

public import ArtGallery.Orthogonal.BoundaryPoint.PinGridSound
public import ArtGallery.Orthogonal.BoundaryPoint.GridSweep

/-! # Auditing a complete pin by pairwise rectangle and edge tests
The integer frame for a pin may exchange coordinates and reverse signs.
Contact with a pocket is restricted to its mouth, and no boundary edge can
meet the open strip above its slot before the chosen clearance. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PinContact
open PinGridData GridPins RoomGrid GridParity GridAtom CorridorProgram

structure Range where
  t₀ : Int
  t₁ : Int
  n₀ : Int
  n₁ : Int

def inRange (r : Range) (t n : Int) := r.t₀≤t ∧ t≤r.t₁ ∧ r.n₀≤n ∧ n≤r.n₁

def interval (f : Bool) (a b : Nat) : Int × Int :=
  let u := signZ f a
  let v := signZ f b
  (min u v,max u v)

def range (p : Pin) (a b : Index) : Range :=
  let A := interval p.frame.negT (line (component p.frame.swap a)) (line (component p.frame.swap b))
  let B := interval p.frame.negN (line (component (!p.frame.swap) a)) (line (component (!p.frame.swap) b))
  ⟨A.1,A.2,B.1,B.2⟩

def rect (p : Pin) (r : Rect Nat) := range p (r.1,r.2.2.1) (r.2.1,r.2.2.2)

private theorem between_signed {a b k : Nat} (v : Bool) (h : Between a b k) :
    (interval v a b).1≤signZ v k ∧ signZ v k≤(interval v a b).2 := by
  rcases h with h|h <;> cases v <;> simp only [interval,signZ,Bool.false_eq_true,ite_false,ite_true] <;> omega

private theorem located (p : Pin) (a b : Index) (X Y : Nat) (hx : Between (line a.1) (line b.1) X)
    (hy : Between (line a.2) (line b.2) Y) :
    inRange (range p a b) (code p.frame.swap p.frame.negT X Y) (code (!p.frame.swap) p.frame.negN X Y) := by
  cases e : p.frame.swap
  · exact ⟨by simpa [range,code,component,e] using (between_signed p.frame.negT hx).1,
      by simpa [range,code,component,e] using (between_signed p.frame.negT hx).2,
      by simpa [range,code,component,e] using (between_signed p.frame.negN hy).1,
      by simpa [range,code,component,e] using (between_signed p.frame.negN hy).2⟩
  · exact ⟨by simpa [range,code,component,e] using (between_signed p.frame.negT hy).1,
      by simpa [range,code,component,e] using (between_signed p.frame.negT hy).2,
      by simpa [range,code,component,e] using (between_signed p.frame.negN hx).1,
      by simpa [range,code,component,e] using (between_signed p.frame.negN hx).2⟩

private theorem inside (p : Pin) (r : Rect Nat) (X Y : Nat) (h : inBox X Y r=true) :
    inRange (rect p r) (code p.frame.swap p.frame.negT X Y) (code (!p.frame.swap) p.frame.negN X Y) := by
  obtain ⟨a,b,c,d⟩ := of_decide_eq_true h
  exact located p _ _ _ _ (Or.inl ⟨a,b⟩) (Or.inl ⟨c,d⟩)

def apart (a b : Range) := decide (a.t₁<b.t₀ ∨ b.t₁<a.t₀ ∨ a.n₁<b.n₀ ∨ b.n₁<a.n₀)
def onlyHere (a b : Range) (tangent : Bool) (z : Int) :=
  apart a b || if tangent then decide ((z≤a.t₀ ∨ z≤b.t₀) ∧ (a.t₁≤z ∨ b.t₁≤z))
    else decide ((z≤a.n₀ ∨ z≤b.n₀) ∧ (a.n₁≤z ∨ b.n₁≤z))

private theorem contact {a b : Range} {t n z : Int} (axis : Bool) (h : onlyHere a b axis z=true)
    (ha : inRange a t n) (hb : inRange b t n) : (if axis then t else n)=z := by
  unfold inRange at ha hb
  cases axis <;> simp only [onlyHere,apart,Bool.or_eq_true,decide_eq_true_eq,ite_true,ite_false,Bool.false_eq_true] at h ⊢ <;> omega

def wallOK (p : Pin) (e : Index × Index) :=
  let b := range p e.1 e.2
  decide (b.t₁<p.T (line p.low) ∨ p.T (line p.high)<b.t₀ ∨ b.n₁≤p.N (line p.floor) ∨ p.N (line p.clear)≤b.n₀)

def check (p : Pin) (rs : List (Rect Nat)) (cycle : List Index) : Bool :=
  let S := rect p p.shaft
  let C := rect p p.cap
  let lo := p.T (line p.low); let hi := p.T (line p.high)
  decide (lo≤S.t₀ ∧ S.t₁≤hi) &&
  (decide (C.t₁<lo ∨ hi<C.t₀) &&
   (decide (p.N (line p.floor)≤C.n₀ ∧ C.n₁≤p.N (line p.top)) &&
    ((rest p.shaft rs).all (fun r => onlyHere S (rect p r) false (p.N (line p.nearS))) &&
     ((rest p.cap rs).all (fun r => onlyHere C (rect p r) true (p.T (line p.nearC))) &&
      (GridSweep.allEdges cycle).all (wallOK p)))))

/-- `check` over an explicit edge list (the cycle's edges proved once per chart, instead of the
quadratic `allEdges` inside every check). -/
def checkE (p : Pin) (rs : List (Rect Nat)) (E : List GridSweep.Edge) : Bool :=
  let S := rect p p.shaft
  let C := rect p p.cap
  let lo := p.T (line p.low); let hi := p.T (line p.high)
  decide (lo≤S.t₀ ∧ S.t₁≤hi) &&
  (decide (C.t₁<lo ∨ hi<C.t₀) &&
   (decide (p.N (line p.floor)≤C.n₀ ∧ C.n₁≤p.N (line p.top)) &&
    ((rest p.shaft rs).all (fun r => onlyHere S (rect p r) false (p.N (line p.nearS))) &&
     ((rest p.cap rs).all (fun r => onlyHere C (rect p r) true (p.T (line p.nearC))) &&
      E.all (wallOK p)))))

theorem check_of_edges {p : Pin} {rs : List (Rect Nat)} {cycle : List Index} {E : List GridSweep.Edge}
    (hE : GridSweep.allEdges cycle=E) (h : checkE p rs E=true) : check p rs cycle=true := by
  subst hE; exact h

theorem sound {p : Pin} {rs : List (Rect Nat)} {l : List Index} (ok : check p rs l=true) (X Y : Nat) :
    p.At rs l X Y := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨shaft,skip,cap,shaftOnly,capOnly,walls⟩ := ok
  let t := code p.frame.swap p.frame.negT X Y
  let n := code (!p.frame.swap) p.frame.negN X Y
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro hit
    have h := inside p p.shaft X Y hit
    exact ⟨shaft.1.trans h.1,h.2.1.trans shaft.2⟩
  · intro hit ne
    by_contra bad
    have was : (rest p.shaft rs).any (inBox X Y)=true := by simpa using bad
    obtain ⟨r,hr,view⟩ := List.any_eq_true.mp was
    exact ne (contact false (List.all_eq_true.mp shaftOnly r hr) (inside p _ _ _ hit) (inside p _ _ _ view))
  · intro hit strip
    have h := inside p p.cap X Y hit
    unfold inRange at h
    rcases skip with left|right <;> omega
  · intro hit any
    obtain ⟨r,hr,view⟩ := List.any_eq_true.mp any
    have h := inside p _ _ _ hit
    exact ⟨contact true (List.all_eq_true.mp capOnly r hr) h (inside p _ _ _ view),cap.1.trans h.2.2.1,h.2.2.2.trans cap.2⟩
  · intro strip above below
    by_contra fail
    have bound : boundaryB l X Y=true := by simpa using fail
    obtain ⟨i,hi,edge⟩ := List.any_eq_true.mp bound
    let a := aidx l i
    let b := bidx l i
    have he : (a,b)∈GridSweep.allEdges l := List.mem_map.mpr ⟨i,hi,rfl⟩
    have tests := of_decide_eq_true (List.all_eq_true.mp walls (a,b) he)
    obtain ⟨hx,hy⟩ := of_decide_eq_true edge
    have h := located p a b X Y hx hy
    unfold inRange at h
    dsimp only at tests
    omega

end ArtGallery.Orthogonal.BoundaryPoint.PinContact
end
