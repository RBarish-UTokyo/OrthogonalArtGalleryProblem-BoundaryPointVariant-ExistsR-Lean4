module

public import ArtGallery.Orthogonal.BoundaryPoint.SourcePortPlan
public import ArtGallery.Orthogonal.BoundaryPoint.BankCoordinates
public import Mathlib.Data.List.Sort

/-! # Numeric slots for the source compiler

Only slots actually mentioned by the lowered equations occupy the hub.
Repeated occurrences have a single master position. Within-bank ranks are
indices in a duplicate-free list, and every rank and door index is bounded
by the common size parameter. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PhysicalLayout
open SourcePortPlan PrimitiveNetwork FlattenNetwork PrivatePorts

def localCount {ι} : Net ι → Nat
  | .atom _ => 0
  | .bind t => 1+localCount t
  | .both a b => localCount a+localCount b

def localIndex {ι} (p : Net ι) : locals p → Nat :=
  match p with
  | .atom _ => fun x => nomatch x
  | .bind t => fun | .inl _ => 0 | .inr j => 1+localIndex t j
  | .both a b => fun | .inl i => localIndex a i | .inr j => localCount a+localIndex b j

def decLocal {ι} (p : Net ι) : DecidableEq (locals p) :=
  match p with
  | .atom _ => inferInstanceAs (DecidableEq Empty)
  | .bind t =>
    letI := decLocal t
    inferInstanceAs (DecidableEq (Unit ⊕ locals t))
  | .both a b =>
    letI := decLocal a
    letI := decLocal b
    inferInstanceAs (DecidableEq (locals a ⊕ locals b))

instance (Φ : List ETRINV.Constraint) : DecidableEq (Master Φ) := by
  letI (i : Fin Φ.length) : DecidableEq (locals (lowerConstraint Φ[i])) := decLocal _
  unfold Master
  infer_instance

deriving instance DecidableEq for Port
deriving instance DecidableEq for Slot

abbrev Label (Φ : List ETRINV.Constraint) := Slot (Master Φ) (Fin (logical Φ).length)

def portNumber : Port → Nat | .first => 0 | .second => 1 | .third => 2

/-- The arithmetic order creates each complemented value followed by its
reciprocal. The logical addition network binds the three complements first. -/
def localOrder (op : ETRINV.Constraint) (j : Nat) : Nat :=
  match op with
  | .add .. => if j<3 then 2*j else 2*(j-3)+1
  | _ => j

def key {Φ : List ETRINV.Constraint} (s : Label Φ) : List Nat :=
  bank s :: (match s with
  | .master (.inl i) => [0,i]
  | .master (.inr ⟨i,j⟩) => [1,i.val,localOrder Φ[i] (localIndex _ j)]
  | .half => []
  | .privatePort r k | .middle r k => [r.val,portNumber k]
  | .reciprocal r k b => [r.val,portNumber k,if b then 1 else 0])

def args {σ} : Leaf σ → List σ
  | .invLe a b | .invRevGe a b => [a,b]
  | .ordinary a b z | .lower a b z | .shifted a b z => [a,b,z]

def slots (Φ : List ETRINV.Constraint) : List (Label Φ) :=
  ((leaves Φ).flatMap args).dedup.mergeSort (fun a b => decide (key a ≤ key b))

def slotsOfBank {Φ : List ETRINV.Constraint} (ss : List (Label Φ)) (b : Nat) :=
  ss.filter (fun s => bank s == b)
def bankSlots (Φ : List ETRINV.Constraint) (b : Nat) := slotsOfBank (slots Φ) b
def rankIn {Φ : List ETRINV.Constraint} (ss : List (Label Φ)) (s : Label Φ) :=
  (slotsOfBank ss (bank s)).idxOf s
def rank {Φ : List ETRINV.Constraint} (s : Label Φ) := rankIn (slots Φ) s

/-- The output size is at least the number of wings and the number of slots.
The empty input is handled with a fixed square by the word generator. -/
def size (Φ : List ETRINV.Constraint) := max (leaves Φ).length (slots Φ).length

theorem mem_slots {Φ l} (hl : l ∈ leaves Φ) {s} (hs : s ∈ args l) : s ∈ slots Φ := by
  simpa [slots] using (List.mem_flatMap.mpr ⟨l,hl,hs⟩ : s ∈ (leaves Φ).flatMap args)

theorem mem_bankSlots {Φ s} (hs : s ∈ slots Φ) : s ∈ bankSlots Φ (bank s) := by
  simp [bankSlots,slotsOfBank,hs]

theorem rank_lt {Φ s} (hs : s ∈ slots Φ) : rank s < size Φ := by
  unfold rank rankIn size
  exact (List.idxOf_lt_length_of_mem (mem_bankSlots hs)).trans_le
    ((List.length_filter_le _ _).trans (le_max_right _ _))

theorem distinct_address {Φ} {s t : Label Φ} (hs : s ∈ slots Φ) (ht : t ∈ slots Φ)
    (hb : bank s = bank t) (hi : rank s = rank t) : s=t := by
  let b := bank t
  have hS : s ∈ bankSlots Φ b := by simpa only [hb,b] using mem_bankSlots hs
  have hT : t ∈ bankSlots Φ b := mem_bankSlots ht
  have idx : (bankSlots Φ b).idxOf s=(bankSlots Φ b).idxOf t := by
    simpa only [rank,rankIn,bankSlots,hb,b] using hi
  have hleft := List.getElem_idxOf (xs := bankSlots Φ b) (List.idxOf_lt_length_of_mem hS)
  have hright := List.getElem_idxOf (xs := bankSlots Φ b) (List.idxOf_lt_length_of_mem hT)
  simp only [idx] at hleft
  exact hleft.symm.trans hright

def position {Φ} (s : Label Φ) : ℚ := BankCoordinates.slotX (size Φ) (bank s) (rank s)

theorem row_lt {Φ} (i : Fin (leaves Φ).length) : i.val < size Φ :=
  i.isLt.trans_le (le_max_left _ _)

end ArtGallery.Orthogonal.BoundaryPoint.PhysicalLayout
end
