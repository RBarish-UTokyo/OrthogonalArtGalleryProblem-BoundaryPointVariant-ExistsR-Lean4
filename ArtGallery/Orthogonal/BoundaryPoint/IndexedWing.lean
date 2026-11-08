module

public import ArtGallery.Orthogonal.BoundaryPoint.RegisterAlias

/-! # Reading every physical rectangle and guard record on the ordered wing grid -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.IndexedWing
open CorridorProgram MarginCert LinearRegister RegisterTable RegisterOrder RegisterAlias
open ShapeRefs BoundaryChart WingEnvelope ChartDrawing

def entries {α β : Type} (f : α → β → Bool) : List α → List β → Bool
  | [],[] => true
  | a::as,b::bs => f a b && entries f as bs
  | _,_ => false

private theorem entries_map {α β γ : Type} {f : α → β → Bool} {x : α → γ} {y : β → γ}
    (good : ∀ a b,f a b=true → x a=y b) (l : List α) (r : List β) (ok : entries f l r=true) :
    l.map x=r.map y := by
  induction l generalizing r with
  | nil => cases r <;> first | rfl | contradiction
  | cons a l ih =>
    cases r with
    | nil => contradiction
    | cons b r =>
      have h : f a b=true ∧ entries f l r=true := by simpa only [entries,Bool.and_eq_true] using ok
      simp only [List.map_cons,good a b h.1,ih r h.2]

def checkData {α β : Type} (x y : α → β → Bool) (left : Data α) (right : Data β) :=
  entries (fun a b => (x a.1 b.1 && x a.2.1 b.2.1) && (y a.2.2.1 b.2.2.1 && y a.2.2.2 b.2.2.2)) left.1 right.1 &&
    entries (entries (fun a b => x a.1 b.1 && y a.2 b.2)) left.2 right.2

theorem data_map {A B C : Type} (x y : A → B → Bool) (f g : A → C) (u v : B → C)
    (hx : ∀ a b,x a b=true → f a=u b) (hy : ∀ a b,y a b=true → g a=v b)
    {a : Data A} {b : Data B} (ok : checkData x y a b=true) : mapData f g a=mapData u v b := by
  have pair := (Bool.and_eq_true_iff.mp ok)
  apply Prod.ext
  · apply entries_map _ _ _ pair.1
    intro r s found
    have h : (x r.1 s.1=true ∧ x r.2.1 s.2.1=true) ∧ (y r.2.2.1 s.2.2.1=true ∧ y r.2.2.2 s.2.2.2=true) := by
      simpa only [Bool.and_eq_true] using found
    exact Prod.ext (hx _ _ h.1.1) (Prod.ext (hx _ _ h.1.2) (Prod.ext (hy _ _ h.2.1) (hy _ _ h.2.2)))
  · apply entries_map _ _ _ pair.2
    intro l r found; apply entries_map _ _ _ found
    intro p q h
    have hh : x p.1 q.1=true ∧ y p.2 q.2=true := by simpa only [Bool.and_eq_true] using h
    exact Prod.ext (hx _ _ hh.1) (hy _ _ hh.2)

def refsFor (t : Template) (y : Bool) := selected (pool y (refs t)) (idsOf t y)
def axisMatch (t : Template) (rs : List Row) (cache : List Entry) (y : Bool) (r : Ref) (i : Nat) :=
  equivalent rs cache (axisOf t y) r ((refsFor t y).getD i 0)

def check (t : Template) (rs : List Row) (cache : List Entry) (index : Data Nat) :=
  checkData (axisMatch t rs cache false) (axisMatch t rs cache true) (refs t) index

def grid (t : Template) (args : List ℚ) (y : Bool) : List ℚ :=
  selected (pool y (ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0)))) (idsOf t y)

theorem grid_value {t : Template} {args xs rs bs cache} (m : Model args xs rs bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) (y : Bool) (i : Nat) :
    (grid t args y).getD i 0=readRef xs (axisOf t y) (getRat args 0) ((refsFor t y).getD i 0) := by
  subst xs
  rw [grid,ShapeRefs.levels]
  exact List.getD_map (l:=refsFor t y) (n:=i) (d:=0) (readRef _ (axisOf t y) _)

theorem realized {t : Template} {args xs rs bs cache} (m : Model args xs rs bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) (index : Data Nat)
    (pass : check t rs cache index=true) :
    ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))=
      mapData (fun i => (grid t args false).getD i 0) (fun i => (grid t args true).getD i 0) index := by
  rw [←ShapeRefs.coords,←run]
  apply data_map _ _ _ _ _ _ _ _ pass
  · intro a b ok; rw [grid_value m run]; exact RegisterAlias.equal m _ ok
  · intro a b ok; rw [grid_value m run]; exact RegisterAlias.equal m _ ok

end ArtGallery.Orthogonal.BoundaryPoint.IndexedWing
end
