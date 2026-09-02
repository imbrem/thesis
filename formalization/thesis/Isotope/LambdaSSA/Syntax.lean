import Isotope.LambdaIter.Signature

/-!
# Raw lambda-SSA syntax

This is the first modern port of `DeBruijnSSA.BinSyntax`.  Value variables and
block labels are separate de Bruijn namespaces.  The syntax is deliberately
independent of the legacy categorical hierarchy.
-/

namespace Isotope.LambdaSSA

/-- Lift a renaming through one newly-bound de Bruijn variable. -/
def lift (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Lift a renaming through `n` newly-bound variables. -/
def liftN : Nat → (Nat → Nat) → Nat → Nat
  | 0, ρ => ρ
  | n + 1, ρ => lift (liftN n ρ)

/-- Pure expressions. Operations are parameterized by the instruction set `Φ`. -/
inductive Tm (Φ : Type u) where
  | var (index : Nat)
  | op (opcode : Φ) (arg : Tm Φ)
  | let₁ (value body : Tm Φ)
  | pair (left right : Tm Φ)
  | unit
  | let₂ (value body : Tm Φ)
  | inl (value : Tm Φ)
  | inr (value : Tm Φ)
  | case (discr left right : Tm Φ)
  | abort (value : Tm Φ)
  deriving Repr, DecidableEq

namespace Tm

/-- Rename free value variables. -/
def rename (ρ : Nat → Nat) : Tm Φ → Tm Φ
  | .var i => .var (ρ i)
  | .op f a => .op f (a.rename ρ)
  | .let₁ a b => .let₁ (a.rename ρ) (b.rename (lift ρ))
  | .pair a b => .pair (a.rename ρ) (b.rename ρ)
  | .unit => .unit
  | .let₂ a b => .let₂ (a.rename ρ) (b.rename (liftN 2 ρ))
  | .inl a => .inl (a.rename ρ)
  | .inr a => .inr (a.rename ρ)
  | .case a l r => .case (a.rename ρ) (l.rename (lift ρ)) (r.rename (lift ρ))
  | .abort a => .abort (a.rename ρ)

/-- Lift a simultaneous substitution through one binder. -/
def liftSubst (σ : Nat → Tm Φ) : Nat → Tm Φ
  | 0 => .var 0
  | n + 1 => (σ n).rename Nat.succ

/-- Lift a simultaneous substitution through `n` binders. -/
def liftSubstN : Nat → (Nat → Tm Φ) → Nat → Tm Φ
  | 0, σ => σ
  | n + 1, σ => liftSubst (liftSubstN n σ)

/-- Simultaneous substitution of free value variables. -/
def subst (σ : Nat → Tm Φ) : Tm Φ → Tm Φ
  | .var i => σ i
  | .op f a => .op f (a.subst σ)
  | .let₁ a b => .let₁ (a.subst σ) (b.subst (liftSubst σ))
  | .pair a b => .pair (a.subst σ) (b.subst σ)
  | .unit => .unit
  | .let₂ a b => .let₂ (a.subst σ) (b.subst (liftSubstN 2 σ))
  | .inl a => .inl (a.subst σ)
  | .inr a => .inr (a.subst σ)
  | .case a l r => .case (a.subst σ) (l.subst (liftSubst σ)) (r.subst (liftSubst σ))
  | .abort a => .abort (a.subst σ)

/-- Substitute a term for de Bruijn variable zero. -/
def subst0 (a : Tm Φ) : Nat → Tm Φ
  | 0 => a
  | n + 1 => .var n

end Tm

/-- A straight-line sequence of SSA definitions. -/
inductive Body (Φ : Type u) where
  | nil
  | let₁ (value : Tm Φ) (rest : Body Φ)
  | let₂ (value : Tm Φ) (rest : Body Φ)
  deriving Repr, DecidableEq

namespace Body

def bound : Body Φ → Nat
  | .nil => 0
  | .let₁ _ b => b.bound + 1
  | .let₂ _ b => b.bound + 2

def rename (ρ : Nat → Nat) : Body Φ → Body Φ
  | .nil => .nil
  | .let₁ a b => .let₁ (a.rename ρ) (b.rename (lift ρ))
  | .let₂ a b => .let₂ (a.rename ρ) (b.rename (liftN 2 ρ))

def subst (σ : Nat → Tm Φ) : Body Φ → Body Φ
  | .nil => .nil
  | .let₁ a b => .let₁ (a.subst σ) (b.subst (Tm.liftSubst σ))
  | .let₂ a b => .let₂ (a.subst σ) (b.subst (Tm.liftSubstN 2 σ))

@[simp] theorem bound_rename (b : Body Φ) (ρ : Nat → Nat) :
    (b.rename ρ).bound = b.bound := by
  induction b generalizing ρ <;> simp [rename, bound, *]

@[simp] theorem bound_subst (b : Body Φ) (σ : Nat → Tm Φ) :
    (b.subst σ).bound = b.bound := by
  induction b generalizing σ <;> simp [subst, bound, *]

end Body

/-- Control transfer at the end of a block. -/
inductive Terminator (Φ : Type u) where
  | br (label : Nat) (arg : Tm Φ)
  | case (discr : Tm Φ) (left right : Terminator Φ)
  deriving Repr, DecidableEq

namespace Terminator

def renameVars (ρ : Nat → Nat) : Terminator Φ → Terminator Φ
  | .br ℓ a => .br ℓ (a.rename ρ)
  | .case a l r => .case (a.rename ρ) (l.renameVars (lift ρ)) (r.renameVars (lift ρ))

def renameLabels (ρ : Nat → Nat) : Terminator Φ → Terminator Φ
  | .br ℓ a => .br (ρ ℓ) a
  | .case a l r => .case a (l.renameLabels ρ) (r.renameLabels ρ)

def substVars (σ : Nat → Tm Φ) : Terminator Φ → Terminator Φ
  | .br ℓ a => .br ℓ (a.subst σ)
  | .case a l r =>
      .case (a.subst σ) (l.substVars (Tm.liftSubst σ)) (r.substVars (Tm.liftSubst σ))

end Terminator

/-- A straight-line body followed by a terminator. -/
structure Block (Φ : Type u) where
  body : Body Φ
  terminator : Terminator Φ
  deriving Repr, DecidableEq

namespace Block

def renameVars (ρ : Nat → Nat) (b : Block Φ) : Block Φ :=
  ⟨b.body.rename ρ, b.terminator.renameVars (liftN b.body.bound ρ)⟩

def renameLabels (ρ : Nat → Nat) (b : Block Φ) : Block Φ :=
  ⟨b.body, b.terminator.renameLabels ρ⟩

def substVars (σ : Nat → Tm Φ) (b : Block Φ) : Block Φ :=
  ⟨b.body.subst σ, b.terminator.substVars (Tm.liftSubstN b.body.bound σ)⟩

end Block

/-- Single-entry, multiple-exit regions with mutually recursive CFG binding. -/
inductive Region (Φ : Type u) where
  | br (label : Nat) (arg : Tm Φ)
  | case (discr : Tm Φ) (left right : Region Φ)
  | let₁ (value : Tm Φ) (body : Region Φ)
  | let₂ (value : Tm Φ) (body : Region Φ)
  | cfg (entry : Region Φ) (arity : Nat) (blocks : Fin arity → Region Φ)

namespace Region

def renameVars (ρ : Nat → Nat) : Region Φ → Region Φ
  | .br ℓ a => .br ℓ (a.rename ρ)
  | .case a l r => .case (a.rename ρ) (l.renameVars (lift ρ)) (r.renameVars (lift ρ))
  | .let₁ a r => .let₁ (a.rename ρ) (r.renameVars (lift ρ))
  | .let₂ a r => .let₂ (a.rename ρ) (r.renameVars (liftN 2 ρ))
  | .cfg e n bs => .cfg (e.renameVars ρ) n (fun i => (bs i).renameVars (lift ρ))

def renameLabels (ρ : Nat → Nat) : Region Φ → Region Φ
  | .br ℓ a => .br (ρ ℓ) a
  | .case a l r => .case a (l.renameLabels ρ) (r.renameLabels ρ)
  | .let₁ a r => .let₁ a (r.renameLabels ρ)
  | .let₂ a r => .let₂ a (r.renameLabels ρ)
  | .cfg e n bs =>
      .cfg (e.renameLabels (liftN n ρ)) n (fun i => (bs i).renameLabels (liftN n ρ))

def substVars (σ : Nat → Tm Φ) : Region Φ → Region Φ
  | .br ℓ a => .br ℓ (a.subst σ)
  | .case a l r =>
      .case (a.subst σ) (l.substVars (Tm.liftSubst σ)) (r.substVars (Tm.liftSubst σ))
  | .let₁ a r => .let₁ (a.subst σ) (r.substVars (Tm.liftSubst σ))
  | .let₂ a r => .let₂ (a.subst σ) (r.substVars (Tm.liftSubstN 2 σ))
  | .cfg e n bs =>
      .cfg (e.substVars σ) n (fun i => (bs i).substVars (Tm.liftSubst σ))

/-- Simultaneous substitution for labels.  Each replacement region has one
distinguished value variable, which receives the argument of the branch. -/
abbrev LabelSubst (Φ : Type u) := Nat → Region Φ

namespace LabelSubst

def id : LabelSubst Φ := fun ℓ => .br ℓ (.var 0)

def liftVars (σ : LabelSubst Φ) : LabelSubst Φ :=
  fun ℓ => (σ ℓ).renameVars (LambdaSSA.lift Nat.succ)

def lift (σ : LabelSubst Φ) : LabelSubst Φ
  | 0 => .br 0 (.var 0)
  | ℓ + 1 => (σ ℓ).renameLabels Nat.succ

def liftN : Nat → LabelSubst Φ → LabelSubst Φ
  | 0, σ => σ
  | n + 1, σ => lift (liftN n σ)

end LabelSubst

def substLabels (σ : LabelSubst Φ) : Region Φ → Region Φ
  | .br ℓ a => (σ ℓ).substVars (Tm.subst0 a)
  | .case a l r =>
      .case a (l.substLabels σ.liftVars) (r.substLabels σ.liftVars)
  | .let₁ a r => .let₁ a (r.substLabels σ.liftVars)
  | .let₂ a r => .let₂ a (r.substLabels σ.liftVars.liftVars)
  | .cfg e n bs =>
      .cfg (e.substLabels (σ.liftN n)) n
        (fun i => (bs i).substLabels (σ.liftN n).liftVars)

end Region

end Isotope.LambdaSSA
