module

public import ArtGallery.Orthogonal.BoundaryPoint.PhysicalLayout
public import ArtGallery.Orthogonal.BoundaryPoint.BankCorridor.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.BankCorridor.InvLe_1_360
public import ArtGallery.Orthogonal.BoundaryPoint.BankCorridor.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.BankCorridor.InvLe_1_520
public import ArtGallery.Orthogonal.BoundaryPoint.BankCorridor.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.BankCorridor.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.BankCorridor.InvRevGe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.BankCorridor.Lower_10_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.BankCorridor.Lower_10_360_1000
public import ArtGallery.Orthogonal.BoundaryPoint.BankCorridor.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.BankCorridor.Lower_10_520_1000
public import ArtGallery.Orthogonal.BoundaryPoint.BankCorridor.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.BankCorridor.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.BankCorridor.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.RoomFamily.InvLe
public import ArtGallery.Orthogonal.BoundaryPoint.RoomFamily.InvRevGe
public import ArtGallery.Orthogonal.BoundaryPoint.RoomFamily.Lower
public import ArtGallery.Orthogonal.BoundaryPoint.RoomFamily.Ordinary
public import ArtGallery.Orthogonal.BoundaryPoint.RoomFamily.Shifted

/-! # Placing the private wings of a source instance

The compiler uses the validated port profiles. Each wing is represented by
its free rectangles. The shared hub is the union of the high ceiling steps,
the lower intervening spans, the floor bays and their forcing pockets.
-/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PlanGeometry

open PrivatePorts PhysicalLayout SourcePortPlan BankCoordinates CorridorProgram RoomCoordinates

def Supported {ι row} (l : Leaf (Slot ι row)) : Prop :=
  match l with
  | .ordinary a b z | .shifted a b z => bank a=40 ∧ bank b=200 ∧ bank z=520
  | .lower a b c => bank c=1000 ∧ ((bank a=40 ∧ bank b=200) ∨
        (bank a=10 ∧ bank b ∈ [40,200,360,520]))
  | .invLe a b => (bank a=40 ∧ bank b=200) ∨ (bank a=1 ∧ bank b ∈ [40,200,360,520])
  | .invRevGe a b => (bank a=40 ∧ bank b=200) ∨ (bank a=1 ∧ bank b=10)

theorem supported_row {ι row} (r : row) (a : PrimitiveNetwork.Atom ι) :
    ∀ l ∈ lowerRow r a, Supported l := by
  intro l hl
  rcases List.mem_append.mp hl with hw | hp
  · obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp hw
    cases k <;> simp only [wire,List.mem_cons,List.not_mem_nil,or_false] at hk <;>
      rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Supported,bank]
  · obtain rfl := List.mem_singleton.mp hp
    cases a <;> simp [payload,Supported,bank]

theorem supported {Φ : List ETRINV.Constraint} {l} (hl : l ∈ leaves Φ) : Supported l := by
  obtain ⟨t,ht,hm⟩ := List.mem_flatten.mp hl
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
  exact supported_row i _ l hm

def corridor {Φ : List ETRINV.Constraint} : Leaf (Label Φ) → Layout
  | .ordinary .. => BankCorridor.Ordinary_40_200_520.layout
  | .shifted .. => BankCorridor.Shifted_40_200_520.layout
  | .lower a b _ =>
    if bank a=40 then BankCorridor.Lower_40_200_1000.layout else
    match bank b with
    | 40 => BankCorridor.Lower_10_40_1000.layout
    | 200 => BankCorridor.Lower_10_200_1000.layout
    | 360 => BankCorridor.Lower_10_360_1000.layout
    | _ => BankCorridor.Lower_10_520_1000.layout
  | .invLe a b =>
    if bank a=40 then BankCorridor.InvLe_40_200.layout else
    match bank b with
    | 40 => BankCorridor.InvLe_1_40.layout
    | 200 => BankCorridor.InvLe_1_200.layout
    | 360 => BankCorridor.InvLe_1_360.layout
    | _ => BankCorridor.InvLe_1_520.layout
  | .invRevGe a _ =>
    if bank a=40 then BankCorridor.InvRevGe_40_200.layout else BankCorridor.InvRevGe_1_10.layout

structure ArithmeticRoom where
  x : Axis
  y : Axis
  cells : List (Rect Nat)
  roles : List (List RoomGrid.Index)

def room {σ} : Leaf σ → ArithmeticRoom
  | .invLe .. => ⟨RoomFamily.InvLe.xAxis,RoomFamily.InvLe.yAxis,RoomFamily.InvLe.cells,RoomFamily.InvLe.roles⟩
  | .invRevGe .. => ⟨RoomFamily.InvRevGe.xAxis,RoomFamily.InvRevGe.yAxis,RoomFamily.InvRevGe.cells,RoomFamily.InvRevGe.roles⟩
  | .lower .. => ⟨RoomFamily.Lower.xAxis,RoomFamily.Lower.yAxis,RoomFamily.Lower.cells,RoomFamily.Lower.roles⟩
  | .ordinary .. => ⟨RoomFamily.Ordinary.xAxis,RoomFamily.Ordinary.yAxis,RoomFamily.Ordinary.cells,RoomFamily.Ordinary.roles⟩
  | .shifted .. => ⟨RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,RoomFamily.Shifted.cells,RoomFamily.Shifted.roles⟩

def ArithmeticRoom.coords (a : ArithmeticRoom) (s : ℚ) : Data ℚ :=
  let xs := a.x.coordsQ s
  let ys := a.y.coordsQ s
  let pt := fun (j : Nat × Nat) => (xs.getD j.1 0,ys.getD j.2 0)
  (a.cells.map (fun j => (xs.getD j.1 0,xs.getD j.2.1 0,ys.getD j.2.2.1 0,ys.getD j.2.2.2 0)),
   a.roles.map (fun r => r.map pt))

def wingWith {Φ : List ETRINV.Constraint} (getRank : Label Φ → Nat) (n j : Nat) (l : Leaf (Label Φ)) : Data ℚ :=
  let s := (1:ℚ)/n
  let inputs := s::((j:ℚ)*s)::((args l).map fun t => (getRank t : ℚ)*s)
  let c := (corridor l).coords inputs
  let r := (room l).coords s
  (c.1 ++ r.1,c.2 ++ r.2)

def shift (d : ℚ) (r : Rect ℚ) : Rect ℚ := (r.1+d,r.2.1+d,r.2.2.1,r.2.2.2)

def stepCells (n j : Nat) : List (Rect ℚ) :=
  let d := door j
  let f := 1-D n
  [(d-30,d+110,f,1),
   (d+100-1/1000,d+100+1/1000,2*f,f),
   (d+110,d+110+1/10,1-1/10000,1)] ++
  (if j=0 then [] else [(d+110,door (j-1)-30,f,-6)])

def hub (n count : Nat) (ordered : List ℚ) : List (Rect ℚ) :=
  let steps := (List.range count).flatMap (stepCells n)
  let floor := 1-D n
  let right := ordered.getLastD 0+10
  let left := door (count-1)-30
  let bays := ordered.zipIdx.flatMap fun (p,j) =>
    let wall := if j=0 then left else p-2
    let next := ordered[j+1]?.elim right (fun q => q-3)
    [(if j=0 then 110 else wall,next,floor,floor+1/4),
     (p,p+3/2,-6,-6-floor),
     (wall-1/10,wall,floor,floor+1/100000000)]
  steps ++ [(110,right,floor+1/4,-6)] ++ bays

structure Geometry where
  entrances : List (ℚ × List (Rect ℚ))
  commonRoom : List (Rect ℚ)
  budget : Nat

def generate (Φ : List ETRINV.Constraint) : Geometry :=
  if Φ.isEmpty then ⟨[],[(0,1,0,1)],1⟩ else
  let gates := leaves Φ
  let bases := slots Φ
  let n := max gates.length bases.length
  let locate := rankIn bases
  let wings := gates.zipIdx.map fun (g,j) => (door j,wingWith locate n j g)
  let budget := bases.length + (wings.map fun w => w.2.2.length+1).sum
  ⟨wings.map (fun w => (w.1,w.2.1)),hub n gates.length (bases.map fun s => slotX n (bank s) (locate s)),budget⟩

end ArtGallery.Orthogonal.BoundaryPoint.PlanGeometry
end
