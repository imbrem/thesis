import Isotope.LambdaIter.Named.Alpha
import Isotope.LambdaIter.LocallyNameless.Syntax

/-! # Translation from named to locally nameless lambda-iter terms -/

namespace Isotope.LambdaIter.Named

namespace ToLocallyNameless

/-- The names of the binders currently in scope, newest first. `none` records
an anonymous binder: it occupies an index but cannot resolve a named variable. -/
abbrev Scope (ν : Type*) := List (Binder ν)

/-- Resolve a name to the nearest binder carrying it. -/
def Scope.lookup [DecidableEq ν] (x : ν) : (ρ : Scope ν) → Option (Fin ρ.length)
  | [] => none
  | none :: ρ => (ρ.lookup x).map Fin.succ
  | some y :: ρ => if h : x = y then some 0 else (ρ.lookup x).map Fin.succ

@[simp] theorem Scope.lookup_nil [DecidableEq ν] (x : ν) :
    (Scope.lookup x [] : Option (Fin 0)) = none := rfl

@[simp] theorem Scope.lookup_cons_none [DecidableEq ν] (x : ν) (ρ : Scope ν) :
    Scope.lookup x (none :: ρ) = (ρ.lookup x).map Fin.succ := rfl

@[simp] theorem Scope.lookup_cons_self [DecidableEq ν] (x : ν) (ρ : Scope ν) :
    Scope.lookup x (some x :: ρ) = some 0 := by simp [Scope.lookup]

@[simp] theorem Scope.lookup_cons_ne [DecidableEq ν] {x y : ν} (h : x ≠ y)
    (ρ : Scope ν) :
    Scope.lookup x (some y :: ρ) = (ρ.lookup x).map Fin.succ := by
  simp [Scope.lookup, h]

/-- Translate a named term relative to a stack of enclosing named binders.
Names absent from the stack remain free; names present in it become indices. -/
def translate [DecidableEq ν] (ρ : Scope ν) :
    Named.Tm ν Φ → LocallyNameless.Tm ν Φ ρ.length
  | .var x => match ρ.lookup x with
    | some i => .bv i
    | none => .fv x
  | .op f a => .op f (translate ρ a)
  | .let₁ x a b => .let₁ (translate ρ a) (translate (x :: ρ) b)
  | .unit => .unit
  | .pair a b => .pair (translate ρ a) (translate ρ b)
  | .let₂ x y a b => .let₂ (translate ρ a) (translate (y :: x :: ρ) b)
  | .inl a => .inl (translate ρ a)
  | .inr a => .inr (translate ρ a)
  | .case e x a y b =>
      .case (translate ρ e) (translate (x :: ρ) a) (translate (y :: ρ) b)
  | .abort a => .abort (translate ρ a)
  | .iter a x b => .iter (translate ρ a) (translate (x :: ρ) b)

/-- Translation of a term with no enclosing named binders. -/
def translateClosed [DecidableEq ν] (a : Named.Tm ν Φ) :
    LocallyNameless.Tm ν Φ 0 := translate [] a

/-- Two named terms have the same locally nameless image in every enclosing
scope. Quantifying over scopes makes this relation compositional under binders. -/
def SameLocallyNameless [DecidableEq ν] (a b : Named.Tm ν Φ) : Prop :=
  ∀ ρ, translate ρ a = translate ρ b

namespace SameLocallyNameless

variable [DecidableEq ν] {a b c : Named.Tm ν Φ}

@[refl] theorem refl (a : Named.Tm ν Φ) : SameLocallyNameless a a :=
  fun _ => rfl

@[symm] theorem symm (h : SameLocallyNameless a b) : SameLocallyNameless b a :=
  fun ρ => (h ρ).symm

@[trans] theorem trans (h₁ : SameLocallyNameless a b)
    (h₂ : SameLocallyNameless b c) : SameLocallyNameless a c :=
  fun ρ => (h₁ ρ).trans (h₂ ρ)

theorem op (h : SameLocallyNameless a b) :
    SameLocallyNameless (.op f a) (.op f b) :=
  fun ρ => congrArg (LocallyNameless.Tm.op f) (h ρ)

theorem let₁ (ha : SameLocallyNameless a a') (hb : SameLocallyNameless b b') :
    SameLocallyNameless (.let₁ x a b) (.let₁ x a' b') :=
  fun ρ => by simp only [translate, ha ρ, hb (x :: ρ)]

theorem pair (ha : SameLocallyNameless a a') (hb : SameLocallyNameless b b') :
    SameLocallyNameless (.pair a b) (.pair a' b') :=
  fun ρ => by simp only [translate, ha ρ, hb ρ]

theorem let₂ (ha : SameLocallyNameless a a') (hb : SameLocallyNameless b b') :
    SameLocallyNameless (.let₂ x y a b) (.let₂ x y a' b') :=
  fun ρ => by simp only [translate, ha ρ, hb (y :: x :: ρ)]

theorem inl (h : SameLocallyNameless a b) :
    SameLocallyNameless (.inl a) (.inl b) :=
  fun ρ => congrArg LocallyNameless.Tm.inl (h ρ)

theorem inr (h : SameLocallyNameless a b) :
    SameLocallyNameless (.inr a) (.inr b) :=
  fun ρ => congrArg LocallyNameless.Tm.inr (h ρ)

theorem case (he : SameLocallyNameless e e')
    (hl : SameLocallyNameless l l') (hr : SameLocallyNameless r r') :
    SameLocallyNameless (.case e x l y r) (.case e' x l' y r') :=
  fun ρ => by simp only [translate, he ρ, hl (x :: ρ), hr (y :: ρ)]

theorem abort (h : SameLocallyNameless a b) :
    SameLocallyNameless (.abort a) (.abort b) :=
  fun ρ => congrArg LocallyNameless.Tm.abort (h ρ)

theorem iter (ha : SameLocallyNameless a a') (hb : SameLocallyNameless b b') :
    SameLocallyNameless (.iter a x b) (.iter a' x b') :=
  fun ρ => by simp only [translate, ha ρ, hb (x :: ρ)]

theorem translateClosed_eq (h : SameLocallyNameless a b) :
    translateClosed a = translateClosed b := h []

end SameLocallyNameless

@[simp] theorem translateClosed_var [DecidableEq ν] (x : ν) :
    translateClosed (Φ := Φ) (.var x) = .fv x := rfl

@[simp] theorem translate_var_bound [DecidableEq ν] (x : ν) (ρ : Scope ν) :
    translate (some x :: ρ) (Named.Tm.var x : Named.Tm ν Φ) = .bv 0 := by
  simp [translate]

@[simp] theorem translate_var_under_anonymous [DecidableEq ν] (x : ν) (ρ : Scope ν) :
    translate (none :: ρ) (Named.Tm.var x : Named.Tm ν Φ) =
      (translate ρ (.var x)).lift := by
  simp only [translate, Scope.lookup_cons_none, LocallyNameless.Tm.lift]
  cases ρ.lookup x <;> rfl

/-- A single bound occurrence is independent of the chosen binder name. -/
example [DecidableEq ν] (x y : ν) :
    translateClosed (Φ := Φ) (.let₁ (some x) .unit (.var x)) =
      translateClosed (.let₁ (some y) .unit (.var y)) := by
  simp [translateClosed, translate]

/-- Shadowing resolves to the nearest binder. -/
example [DecidableEq ν] (x : ν) :
    translateClosed (Φ := Φ)
        (.let₁ (some x) .unit (.let₁ (some x) .unit (.var x))) =
      .let₁ .unit (.let₁ .unit (.bv 0)) := by
  simp [translateClosed, translate]

/-- An anonymous binder occupies index zero while leaving names free. -/
example [DecidableEq ν] (x : ν) :
    translateClosed (Φ := Φ) (.let₁ none .unit (.var x)) =
      .let₁ .unit (.fv x) := by
  simp [translateClosed, translate]

end ToLocallyNameless

end Isotope.LambdaIter.Named
