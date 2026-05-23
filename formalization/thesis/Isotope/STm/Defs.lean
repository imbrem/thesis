import Isotope.Args.Defs

namespace Isotope

universe uargs uix uval uop

open Args

structure STm.Lang (Arity : Type uargs) [I : Args.{uargs, uix} Arity] where
  Val : Type uval
  Op : Arity -> Type uop

variable {Arity} [I : Args Arity]

universe uatom

inductive STm (L : STm.Lang Arity) (A : Type uatom) where
  | sym : A → STm L A
  | const : L.Val → STm L A
  | op: {arity : Arity} → L.Op arity → (Ix arity → STm L A) → STm L A

namespace STm

namespace Lang

inductive Tag (L : Lang Arity) : Type _
  | val : L.Val → Tag L
  | op {arity} (o : L.Op arity) : Tag L

@[simp]
def Tag.arity? {L : Lang Arity} : Tag L → WithZero Arity
  | .val _ => 0
  | .op (arity := arity) _ => arity

inductive Tag? (L : Lang Arity) (A : Type uatom) : Type _
  | sym (a : A) : Tag? L A
  | val (c : L.Val) : Tag? L A
  | op {arity} (o : L.Op arity) : Tag? L A

@[simp]
def Tag?.arity? {L : Lang Arity} {A : Type uatom} : Tag? L A → WithZero Arity
  | .op (arity := arity) _ => arity
  | _ => 0

end Lang

variable {L : STm.Lang Arity}

variable {A A₁ A₂ A₃}

@[simp]
def arity? : STm L A → Option Arity
  | .op (arity := arity) _ _ => some arity
  | _ => none

@[simp]
def tag? : (e : STm L A) → Option L.Tag
  | .const c => some (.val c)
  | .op o _ => some (.op o)
  | _ => none

-- Coercion

instance instCoeSym : Coe A (STm L A) where
  coe := .sym

instance instCoeVal : Coe L.Val (STm L A) where
  coe := .const

-- Inhabitance

instance instInhabited [Inhabited L.Val] : Inhabited (STm L A) where
  default := .const default

instance instNonemptySym [inst : Nonempty A] : Nonempty (STm L A)
  := inst.elim (fun a => ⟨.sym a⟩)

instance instNonemptyVal [inst : Nonempty L.Val] : Nonempty (STm L A)
  := inst.elim (fun c => ⟨.const c⟩)

-- Monad

@[simp]
def mapSym (f : A → A') : STm L A → STm L A'
  | .sym a => .sym (f a)
  | .const c => .const c
  | .op o es => .op o (fun i => mapSym f (es i))

@[simp]
theorem mapSym_id (e : STm L A) :
  mapSym id e = e := by induction e <;> simp [*]

@[simp]
theorem mapSym_mapSym (f : A₁ → A₂) (g : A₂ → A₃) (e : STm L A₁) :
  mapSym g (mapSym f e) = mapSym (g ∘ f) e := by induction e <;> simp [*]

@[simp]
def substSym (f : A₁ → STm L A₂) : STm L A₁ → STm L A₂
  | .sym a => f a
  | .const c => .const c
  | .op o es => .op o (fun i => substSym f (es i))

@[simp]
theorem substSym_sym_comp (f : A₁ → A₂)
  : substSym (L := L) (.sym ∘ f) = mapSym f := by ext e; induction e <;> simp [*]

@[simp]
theorem substSym_sym (e : STm L A) :
  substSym .sym e = e := by induction e <;> simp [*]

@[simp]
theorem substSym_substSym (f : A₁ → STm L A₂) (g : A₂ → STm L A₃) (e : STm L A₁) :
  substSym g (substSym f e) = substSym (fun a => substSym g (f a)) e := by
  induction e <;> simp [*]

instance instMonad : Monad (STm L) where
  map := mapSym
  pure := .sym
  bind e f := e.substSym f

theorem map_def (f : A₁ → A₂) (e : STm L A₁) :
  f <$> e = e.mapSym f := rfl

@[simp]
theorem map_sym (f : A₁ → A₂) (a : A₁) :
  f <$> (.sym a : STm L A₁) = .sym (f a) := rfl

@[simp]
theorem map_const (f : A₁ → A₂) (c : L.Val) :
  f <$> (.const c : STm L A₁) = .const c := rfl

@[simp]
theorem map_op (f : A₁ → A₂) {arity} (o : L.Op arity) (es : Ix arity → STm L A₁) :
  f <$> (.op o es : STm L A₁) = .op o (fun i => f <$> es i) := rfl

theorem bind_def (e : STm L A₁) (f : A₁ → STm L A₂) :
  e >>= f = e.substSym f := rfl

@[simp]
theorem bind_sym (a : A₁) (f : A₁ → STm L A₂) :
  (.sym a : STm L A₁) >>= f = f a := rfl

@[simp]
theorem bind_const (c : L.Val) (f : A₁ → STm L A₂) :
  (.const c : STm L A₁) >>= f = .const c := rfl

@[simp]
theorem bind_op {arity} (o : L.Op arity) (es : Ix arity → STm L A₁) (f : A₁ → STm L A₂) :
  (.op o es : STm L A₁) >>= f = .op o (es >=> f) := rfl

instance : LawfulMonad (STm L) :=
  LawfulMonad.mk' (STm L)
    (bind_pure_comp := fun f => congrFun (substSym_sym_comp f))
    mapSym_id (fun _ _ => rfl)
    (fun e f g => substSym_substSym f g e)

end STm

end Isotope
