module

public import ArtGallery.Orthogonal.BoundaryPoint.HubTurn
public import ArtGallery.Orthogonal.BoundaryPoint.CompiledSize

/-! # Each numeric wing is matched once by the hub-ceiling splice
The only consecutive vertices at door height are a single horizontal edge
of each hub step. Distinct door addresses differ by at least 2000. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubDoors
open RectContour ContourJoin BoundaryChart BankCoordinates

def high (e : Vertex × Vertex) : Bool := e.1.2==1 && e.2.2==1
def scan (p : Vertex) : List Vertex → List (Vertex × Vertex)
  | [] => []
  | q::l => (if high (p,q) then [(p,q)] else []) ++ scan q l

theorem scan_append (p : Vertex) (l r : List Vertex) :
    scan p (l++r)=scan p l++scan (l.getLastD p) r := by
  induction l generalizing p with
  | nil => simp [scan]
  | cons a l ih =>
    simp only [List.cons_append,scan,ih,List.append_assoc,List.getLastD_cons]

private theorem flat_scan {α : Type} (p : Vertex) (l : List α) (f : α → List Vertex)
    (out : α → List (Vertex × Vertex)) (h : ∀ a∈l, ∀ q,scan q (f a)=out a) :
    scan p (l.flatMap f)=l.flatMap out := by
  induction l generalizing p with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons,scan_append,h a List.mem_cons_self]
    rw [ih _ (fun v hv => h v (List.mem_cons_of_mem _ hv))]

def topEdge (j : Nat) : Vertex × Vertex := ((door j+110+1/10,1),(door j-30,1))

private theorem scan_floor (f : ℚ) (lo : f < -7) (p : Vertex) (j : Nat) :
    scan p (foot f j)=[] := by
  have f1 : f≠1 := by linarith
  have f2 : 2*f≠1 := by linarith
  simp [scan,foot,high,f1,f2]
private theorem scan_divider (f : ℚ) (lo : f < -7) (p : Vertex) (x : ℚ) :
    scan p (divider f x)=[] := by
  have f1 : f≠1 := by linarith
  have f2 : f+1/4≠1 := by linarith
  have f3 : f+1/100000000≠1 := by linarith
  simp only [one_div] at f2 f3
  simp [scan,divider,high,f1,f2,f3]
private theorem scan_shaft (f : ℚ) (lo : f < -7) (p : Vertex) (x : ℚ) :
    scan p (shaft f x)=[] := by
  have f1 : (-6:ℚ)≠1 := by norm_num
  have f2 : -6-f≠1 := by linarith
  simp [scan,shaft,high,f1,f2]
private theorem scan_cap (n j : Nat) (p : Vertex) : scan p (capPath n j)=[topEdge j] := by
  unfold capPath
  split <;> norm_num [high,scan,topEdge]

private theorem skip (l : List Vertex) (h : ∀ v∈l,v.2≠1) (p : Vertex) : scan p l=[] := by
  induction l generalizing p with
  | nil => rfl
  | cons a l ih =>
    have z : high (p,a)=false := by simp [high,h a List.mem_cons_self]
    simp only [scan,z,Bool.false_eq_true,ite_false,List.nil_append]
    exact ih (fun v hv => h v (List.mem_cons_of_mem _ hv)) a

private theorem flat_nil {α β : Type} (l : List α) : l.flatMap (fun _ => ([]:List β))=[] := by
  induction l <;> simp [*]
private theorem flat_one {α β : Type} (l : List α) (f : α → β) : l.flatMap (fun a => [f a])=l.map f := by
  induction l <;> simp [*]

private theorem levels (n count : Nat) (slots : List ℚ) (hn : 65≤n) (p : Vertex) :
    scan p (hubCycle n count slots)=(List.range count).map topEdge := by
  let f := 1-D n
  have h : (65:ℚ)≤n := by exact_mod_cast hn
  have lo : f < -7 := by dsimp [f,D,k]; nlinarith [mul_self_le_mul_self (by norm_num : (0:ℚ)≤65) h]
  have low1 : f≠1 := by linarith
  have low2 : f+1/100000000≠1 := by linarith
  have floor (p) := flat_scan (l:=(List.range count).reverse) p (foot f) (fun _ => [])
    (fun j _ q => scan_floor f lo q j)
  have divs (p) := flat_scan (l:=slots.tail) p (divider f) (fun _ => []) (fun v _ q => scan_divider f lo q v)
  have roof (p) := flat_scan (l:=slots.reverse) p (shaft f) (fun _ => []) (fun v _ q => scan_shaft f lo q v)
  have caps (p) := flat_scan p (List.range count) (capPath count) (fun j => [topEdge j])
    (fun j _ q => scan_cap count j q)
  have start (q : Vertex) : scan q [(door (count-1)-30-1/10,f)]=[] :=
    skip _ (by intro v hv; obtain rfl := List.mem_singleton.mp hv; exact low1) q
  have far (q : Vertex) : scan q [(slots.getLastD 0+10,f),(slots.getLastD 0+10,-6)]=[] := by
    apply skip; intro v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl; exact low1; norm_num
  have close (q : Vertex) : scan q [(door (count-1)-30,f+1/100000000),
      (door (count-1)-30-1/10,f+1/100000000)]=[] := by
    apply skip; intro v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl <;> exact low2
  dsimp only [f] at floor divs roof start far close
  unfold hubCycle; dsimp only
  simp only [scan_append,floor,divs,roof,caps,start,far,close,flat_nil,flat_one,List.nil_append,List.append_nil]

private theorem consecutive (a : Vertex) (l : List Vertex) (close : Vertex) :
    (((a::l).zip (l++[close])).filter high)=scan a (l++[close]) := by
  induction l generalizing a with
  | nil => simp [scan,List.filter_cons]
  | cons b l ih =>
    simp only [List.cons_append,List.zip_cons_cons,List.filter_cons,scan,← ih]
    split <;> rfl

theorem ceiling (n rows : Nat) (slots : List ℚ) (hn : 65≤n) :
    let l := hubCycle n rows slots
    ((l.zip (l.drop 1++l.take 1)).filter high)=(List.range rows).map topEdge := by
  let P := hubCycle n rows slots
  let a : Vertex := (door (rows-1)-30-1/10,1-D n)
  have n65 : (65:ℚ)≤n := by exact_mod_cast hn
  have low : a.2≠1 := by dsimp [a,D,k]; nlinarith [mul_self_le_mul_self (by norm_num : (0:ℚ)≤65) n65]
  have eq : P=a::P.tail := rfl
  change ((P.zip (P.drop 1++P.take 1)).filter high)=_
  calc
    _=scan a (P.tail++[a]) := by
      conv_lhs => rw [eq]
      simpa only [List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero] using consecutive a P.tail a
    _=scan a P.tail := by simp [scan_append,scan,high,low]
    _=scan a P := by conv_rhs => rw [eq]; simp [scan,high,low]
    _=_ := levels n rows slots hn a

theorem slot (n i j : Nat) (hn : 65≤n) (v : List Vertex) :
    compat (W n) (topEdge j) (door i,v) = (i==j) := by
  have nPos : (0:ℚ)<n := by exact_mod_cast (show 0<n by omega)
  have wPos : 0<W n := by unfold W; positivity
  have wSmall : W n≤1 := by
    apply (div_le_iff₀ (show (0:ℚ)<320*n by positivity)).mpr
    have h : (65:ℚ)≤n := by exact_mod_cast hn
    linarith
  apply Bool.eq_iff_iff.mpr
  simp only [compat,topEdge,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,eq_self,true_and]
  constructor
  · rintro ⟨⟨_,lower⟩,upper⟩
    rcases lt_trichotomy i j with h|h|h
    · have sep : (i:ℚ)+1 ≤ j := by exact_mod_cast h
      have U := of_decide_eq_true upper
      unfold door at U
      linarith
    · exact h
    · have sep : (j:ℚ)+1 ≤ i := by exact_mod_cast h
      have L := of_decide_eq_true lower
      unfold door at L
      linarith
  · rintro rfl
    exact ⟨⟨decide_eq_true (by linarith),decide_eq_true (by linarith)⟩,decide_eq_true (by linarith)⟩

end ArtGallery.Orthogonal.BoundaryPoint.HubDoors
end
