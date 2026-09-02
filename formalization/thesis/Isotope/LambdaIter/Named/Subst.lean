import Isotope.LambdaIter.Named.Defs

/-! # Renaming and capture-aware substitution -/

namespace Isotope.LambdaIter.Named


variable {Φ : Type*}

def Tm.rename (ρ : ν → κ) : Tm ν Φ → Tm κ Φ
  | .var x => .var (ρ x)
  | .op f a => .op f (a.rename ρ)
  | .let₁ x a b => .let₁ (x.map ρ) (a.rename ρ) (b.rename ρ)
  | .unit => .unit
  | .pair a b => .pair (a.rename ρ) (b.rename ρ)
  | .let₂ x y a b => .let₂ (x.map ρ) (y.map ρ) (a.rename ρ) (b.rename ρ)
  | .inl a => .inl (a.rename ρ)
  | .inr a => .inr (a.rename ρ)
  | .case e x a y b =>
      .case (e.rename ρ) (x.map ρ) (a.rename ρ) (y.map ρ) (b.rename ρ)
  | .abort a => .abort (a.rename ρ)
  | .iter a x b => .iter (a.rename ρ) (x.map ρ) (b.rename ρ)

variable [DecidableEq ν]

/-- Whether a named binder shadows a particular name. -/
def Binder.blocks (b : Binder ν) (x : ν) : Bool :=
  match b with
  | none => false
  | some y => decide (x = y)

/-- Shadow-respecting substitution. Capture avoidance is expressed separately
by `CaptureSafe`; this operation never substitutes an occurrence shadowed by a
same-named binder. -/
def Tm.subst (x : ν) (s : Tm ν Φ) : Tm ν Φ → Tm ν Φ
  | .var y => if x = y then s else .var y
  | .op f a => .op f (subst x s a)
  | .let₁ y a b =>
      .let₁ y (subst x s a) (if y.blocks x then b else subst x s b)
  | .unit => .unit
  | .pair a b => .pair (subst x s a) (subst x s b)
  | .let₂ y z a b =>
      .let₂ y z (subst x s a)
        (if y.blocks x || z.blocks x then b else subst x s b)
  | .inl a => .inl (subst x s a)
  | .inr a => .inr (subst x s a)
  | .case e y a z b =>
      .case (subst x s e) y (if y.blocks x then a else subst x s a)
        z (if z.blocks x then b else subst x s b)
  | .abort a => .abort (subst x s a)
  | .iter a y b =>
      .iter (subst x s a) y (if y.blocks x then b else subst x s b)

def Tm.Free (x : ν) : Tm ν Φ → Prop
  | .var y => x = y
  | .op _ a | .inl a | .inr a | .abort a => a.Free x
  | .let₁ y a b => a.Free x ∨ (y ≠ some x ∧ b.Free x)
  | .unit => False
  | .pair a b => a.Free x ∨ b.Free x
  | .let₂ y z a b => a.Free x ∨ (y ≠ some x ∧ z ≠ some x ∧ b.Free x)
  | .case e y a z b =>
      e.Free x ∨ (y ≠ some x ∧ a.Free x) ∨ (z ≠ some x ∧ b.Free x)
  | .iter a y b => a.Free x ∨ (y ≠ some x ∧ b.Free x)

def Tm.Binds (x : ν) : Tm ν Φ → Prop
  | .var _ | .unit => False
  | .op _ a | .inl a | .inr a | .abort a => a.Binds x
  | .let₁ y a b => y = some x ∨ a.Binds x ∨ b.Binds x
  | .pair a b => a.Binds x ∨ b.Binds x
  | .let₂ y z a b => y = some x ∨ z = some x ∨ a.Binds x ∨ b.Binds x
  | .case e y a z b =>
      y = some x ∨ z = some x ∨ e.Binds x ∨ a.Binds x ∨ b.Binds x
  | .iter a y b => y = some x ∨ a.Binds x ∨ b.Binds x

/-- A conservative, checkable side condition for the named substitution: no
free name of the replacement is bound anywhere in the target. -/
def CaptureSafe (s t : Tm ν Φ) : Prop :=
  ∀ y, s.Free y → ¬t.Binds y

/-- The capture-avoiding interface requires evidence that the raw,
shadow-respecting traversal cannot capture a free name. -/
def Tm.substSafe (x : ν) (s t : Tm ν Φ) (_ : CaptureSafe s t) : Tm ν Φ :=
  Tm.subst x s t

@[simp] theorem Tm.subst_var_same (x : ν) (s : Tm ν Φ) :
    Tm.subst x s (Tm.var x) = s := by simp [Tm.subst]

@[simp] theorem Tm.subst_var_ne {x y : ν} (h : x ≠ y) (s : Tm ν Φ) :
    Tm.subst x s (Tm.var y) = .var y := by simp [Tm.subst, h]

end Isotope.LambdaIter.Named
