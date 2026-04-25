import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Convert

namespace Isotope

universe uo ua

inductive STerm (O : Type uo) (A : Type ua) where
  | atom : A → STerm O A
  | op: O → {arity : ℕ} → (Fin arity → STerm O A) → STerm O A

namespace STerm

variable {A A' A'' O O' O''}

-- Coercion

instance instCoe : Coe A (STerm O A) where
  coe := .atom

-- Lists

def opL (o : O) (es : List (STerm O A)) : STerm O A := .op o es.get

-- TODO: further opL lore; like for SExp

-- Inhabitance

instance instInhabited [Inhabited A] : Inhabited (STerm O A) where
  default := .atom default

instance instNonempty [inst : Nonempty O] : Nonempty (STerm O A) := inst.elim (fun o => ⟨opL o []⟩)

-- Equality

instance [DecidableEq O] [DecidableEq A] : DecidableEq (STerm O A)
   | .atom a, .atom a' => by simp only [atom.injEq]; infer_instance
   | .op o (arity := n) es, .op o' (arity := n') es' =>
     by
     if h : n = n' then
         cases h; simp only [op.injEq, heq_eq_eq, true_and]
         have hi : ∀ i, Decidable (es i = es' i) := fun i => instDecidableEq (es i) (es' i)
         if h' : o = o' ∧ ∀ i, es i = es' i then
           apply isTrue; convert h'; rw [funext_iff]
         else
           apply isFalse; convert h'; rw [funext_iff]
     else
       apply isFalse; simp [*]
    | .atom _, .op _ _ | .op _ _, .atom _ => isFalse (by simp)

-- Monad

@[simp]
def mapOp (f : O → O') : STerm O A → STerm O' A
  | .atom a => .atom a
  | .op o es => .op (f o) (fun i => mapOp f (es i))

@[simp]
theorem mapOp_id (e : STerm O A) :
  mapOp id e = e := by induction e <;> simp [*]

@[simp]
theorem mapOp_mapOp (f : O → O') (g : O' → O'') (e : STerm O A) :
  mapOp g (mapOp f e) = mapOp (g ∘ f) e := by induction e <;> simp [*]

@[simp]
def mapAtom (f : A → A') : STerm O A → STerm O A'
  | .atom a => .atom (f a)
  | .op o es => .op o (fun i => mapAtom f (es i))

@[simp]
theorem mapAtom_id (e : STerm O A) :
  mapAtom id e = e := by induction e <;> simp [*]

@[simp]
theorem mapAtom_mapAtom (f : A → A') (g : A' → A'') (e : STerm O A) :
  mapAtom g (mapAtom f e) = mapAtom (g ∘ f) e := by induction e <;> simp [*]

@[simp]
def substAtom (f : A → STerm O A') : STerm O A → STerm O A'
  | .atom a => f a
  | .op o es => .op o (fun i => substAtom f (es i))

@[simp]
theorem substAtom_atom_comp (f : A → A')
  : substAtom (O := O) (.atom ∘ f) = mapAtom f := by ext e; induction e <;> simp [*]

@[simp]
theorem substAtom_atom (e : STerm O A) :
  substAtom .atom e = e := by induction e <;> simp [*]

@[simp]
theorem substAtom_substAtom {A''} (f : A → STerm O A') (g : A' → STerm O A'') (e : STerm O A) :
  substAtom g (substAtom f e) = substAtom (fun a => substAtom g (f a)) e := by
  induction e <;> simp [*]

instance instMonad : Monad (STerm O) where
  map := mapAtom
  pure := .atom
  bind e f := e.substAtom f

theorem map_def {A' : Type ua} (f : A → A') (e : STerm O A) :
  f <$> e = e.mapAtom f := rfl

@[simp]
theorem map_atom {A' : Type ua} (f : A → A') (a : A) :
  f <$> (.atom a : STerm O A) = .atom (f a) := rfl

@[simp]
theorem map_op {A' : Type ua} (f : A → A') (o : O) (es : Fin n → STerm O A) :
  f <$> (.op o es : STerm O A) = .op o (fun i => f <$> es i) := rfl

theorem bind_def {A' : Type ua} (e : STerm O A) (f : A → STerm O A') :
  e >>= f = e.substAtom f := rfl

@[simp]
theorem bind_atom {A' : Type ua} (a : A) (f : A → STerm O A') :
  (.atom a : STerm O A) >>= f = f a := rfl

@[simp]
theorem bind_op {A' : Type ua} (o : O) (es : Fin n → STerm O A) (f : A → STerm O A') :
  (.op o es : STerm O A) >>= f = .op o (es >=> f) := rfl

instance : LawfulMonad (STerm O) :=
  LawfulMonad.mk' (STerm O)
    (bind_pure_comp := fun f => congrFun (substAtom_atom_comp f))
    mapAtom_id (fun _ _ => rfl)
    (fun e f g => substAtom_substAtom f g e)

def interpOp
  (atom : A → A')
  (op : O → {arity : ℕ} → (Fin arity → STerm O' A') → STerm O' A')
  : STerm O A → STerm O' A'
  | .atom a => .atom (atom a)
  | .op o es => op o (fun i => interpOp atom op (es i))

end STerm

end Isotope
