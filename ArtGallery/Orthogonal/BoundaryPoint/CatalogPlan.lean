module

public import ArtGallery.Orthogonal.BoundaryPoint.PhysicalLayout
public import ArtGallery.PTime.INVCode
public import ArtGallery.Stade.PTimeRat

/-! # Numeric expansion of bounded ETR-INV words
The three fixed one-equation templates come directly from the private-port
compiler. The public masters are renamed to the actual input variable numbers.
Names local to a clause carry the position of that occurrence, even if two
source equations are identical. Within each fixed bank the number of smaller
distinct names is its physical rank. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CatalogPlan
open PhysicalLayout PrivatePorts SourcePortPlan Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade

abbrev Key := List Nat
abbrev ClauseRows := List (Nat × List Key)
abbrev Row := Nat × List Nat
abbrev Input := List Row × List (Nat × Nat)

/-- Order agrees with the fixed wing catalogue. -/
def style {ι ρ} (l : Leaf (Slot ι ρ)) : Nat :=
  match l with
  | .ordinary .. => 0
  | .shifted .. => 1
  | .lower a b _ => if bank a=40 then 2 else
      if bank b=40 then 3 else if bank b=200 then 4 else if bank b=360 then 5 else 6
  | .invLe a b => if bank a=40 then 12 else
      if bank b=40 then 7 else if bank b=200 then 8 else if bank b=360 then 9 else 10
  | .invRevGe a _ => if bank a=40 then 13 else 11

def schema (e : ETRINV.Constraint) : ClauseRows :=
  (leaves [e]).map (fun l => (style l,(args l).map key))

def rename (j : Nat) (vars : List Nat) (k : Key) : Key :=
  if k.headD 0=1000 then k else
  if k.headD 0=360 then
    if k.getD 1 0=0 then [360,0,vars.getD (k.getD 2 0) 0] else [360,1,j,k.getD 3 0]
  else k.headD 0::j::k.tail

def install (j : Nat) (vars : List Nat) (pattern : ClauseRows) : ClauseRows :=
  pattern.map fun r => (r.1,r.2.map (rename j vars))

def expand (j : Nat) (e : ETRINV.Constraint) : ClauseRows :=
  e.elim (fun x => install j [x] (schema (.one 0)))
    (fun x y z => install j [x,y,z] (schema (.add 0 1 2)))
    (fun x y => install j [x,y] (schema (.inv 0 1)))

def less (u v : Key) : Bool :=
  ((u.zip v).find? (fun p => p.1 != p.2)).elim (decide (u.length<v.length)) (fun p => decide (p.1<p.2))

def bankKeys (keys : List Key) (b : Nat) := keys.filter (fun k => k.headD 0 == b)

def rank (keys : List Key) (k : Key) : Nat :=
  ((bankKeys keys (k.headD 0)).filter (fun l => less l k)).length

def banks : List Nat := [1,10,40,200,360,520,1000]

def address (keys : List Key) : List (Nat × Nat) :=
  banks.flatMap fun b => (List.range (bankKeys keys b).length).map fun i => (b,i)

def compile (eqs : List ETRINV.Constraint) : Input :=
  let rows := eqs.zipIdx.flatMap fun (e,j) => expand j e
  let keys := (rows.flatMap Prod.snd).eraseDups
  (rows.map (fun r => (r.1,r.2.map (rank keys))),address keys)

section Time
variable {α : Type} [Code α]

@[fun_prop] theorem rename_pt {j : α → Nat} {v k : α → List Nat} (hj : PT j) (hv : PT v) (hk : PT k) :
    PT (fun a => rename (j a) (v a) (k a)) := by unfold rename; fun_prop

@[fun_prop] theorem install_pt {j : α → Nat} {v : α → List Nat} {rows : α → ClauseRows}
    (hj : PT j) (hv : PT v) (hr : PT rows) : PT (fun a => install (j a) (v a) (rows a)) := by
  unfold install; fun_prop

@[fun_prop] theorem expand_pt {j : α → Nat} {e : α → ETRINV.Constraint} (hj : PT j) (he : PT e) :
    PT (fun a => expand (j a) (e a)) := by unfold expand; fun_prop

@[fun_prop] theorem less_pt {u v : α → Key} (hu : PT u) (hv : PT v) :
    PT (fun a => less (u a) (v a)) := by unfold less; fun_prop

@[fun_prop] theorem bank_keys_pt {keys : α → List Key} {b : α → Nat} (hk : PT keys) (hb : PT b) :
    PT (fun a => bankKeys (keys a) (b a)) := by unfold bankKeys; fun_prop

@[fun_prop] theorem rank_pt {keys : α → List Key} {k : α → Key} (hks : PT keys) (hk : PT k) :
    PT (fun a => rank (keys a) (k a)) := by unfold rank; fun_prop

@[fun_prop] theorem address_pt {keys : α → List Key} (hk : PT keys) :
    PT (fun a => address (keys a)) := by unfold address; fun_prop

theorem compile_pt {eqs : α → List ETRINV.Constraint} (he : PT eqs) : PT (fun a => compile (eqs a)) := by
  unfold compile; fun_prop

end Time
end ArtGallery.Orthogonal.BoundaryPoint.CatalogPlan
end
